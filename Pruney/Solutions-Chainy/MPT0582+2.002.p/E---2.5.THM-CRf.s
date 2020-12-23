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
% DateTime   : Thu Dec  3 10:51:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  82 expanded)
%              Number of clauses        :   22 (  31 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 369 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t186_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(k1_relat_1(X3),X1)
              & r1_tarski(X3,X2) )
           => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

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

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(k1_relat_1(X3),X1)
                & r1_tarski(X3,X2) )
             => r1_tarski(X3,k7_relat_1(X2,X1)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t186_relat_1])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X15,X13)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(X15,X16),X12)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(k4_tarski(X17,X18),X12)
        | r2_hidden(k4_tarski(X17,X18),X14)
        | X14 != k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | ~ r2_hidden(esk2_3(X12,X13,X14),X13)
        | ~ r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk2_3(X12,X13,X14),X13)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)
        | r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)
        | X14 = k7_relat_1(X12,X13)
        | ~ v1_relat_1(X14)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).

fof(c_0_8,plain,(
    ! [X28,X29] :
      ( ~ v1_relat_1(X28)
      | v1_relat_1(k7_relat_1(X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_9,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X31)
      | ~ r1_tarski(k1_relat_1(X31),X30)
      | k7_relat_1(X31,X30) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_relat_1(esk8_0)
    & r1_tarski(k1_relat_1(esk8_0),esk6_0)
    & r1_tarski(esk8_0,esk7_0)
    & ~ r1_tarski(esk8_0,k7_relat_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( k7_relat_1(esk8_0,esk6_0) = esk8_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_19,negated_conjecture,
    ( ~ r1_tarski(esk8_0,k7_relat_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(k4_tarski(X1,X2),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_15])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),esk5_2(esk8_0,k7_relat_1(esk7_0,esk6_0))),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15])])).

fof(c_0_24,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk8_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),k7_relat_1(X2,esk6_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),k7_relat_1(esk7_0,esk6_0))
    | ~ r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_15]),c_0_23])]),c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.027 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t186_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 0.13/0.38  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 0.13/0.38  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.38  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 0.13/0.38  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.13/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.38  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t186_relat_1])).
% 0.13/0.38  fof(c_0_7, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X15,X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(X15,X16),X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&(~r2_hidden(X17,X13)|~r2_hidden(k4_tarski(X17,X18),X12)|r2_hidden(k4_tarski(X17,X18),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|(~r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12))|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&((r2_hidden(esk2_3(X12,X13,X14),X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.13/0.38  fof(c_0_8, plain, ![X28, X29]:(~v1_relat_1(X28)|v1_relat_1(k7_relat_1(X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.38  fof(c_0_9, plain, ![X30, X31]:(~v1_relat_1(X31)|(~r1_tarski(k1_relat_1(X31),X30)|k7_relat_1(X31,X30)=X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 0.13/0.38  fof(c_0_10, negated_conjecture, (v1_relat_1(esk7_0)&(v1_relat_1(esk8_0)&((r1_tarski(k1_relat_1(esk8_0),esk6_0)&r1_tarski(esk8_0,esk7_0))&~r1_tarski(esk8_0,k7_relat_1(esk7_0,esk6_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.38  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k7_relat_1(X5,X2)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_13, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  fof(c_0_16, plain, ![X21, X22, X23, X24, X25]:((~r1_tarski(X21,X22)|(~r2_hidden(k4_tarski(X23,X24),X21)|r2_hidden(k4_tarski(X23,X24),X22))|~v1_relat_1(X21))&((r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X21)|r1_tarski(X21,X25)|~v1_relat_1(X21))&(~r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X25)|r1_tarski(X21,X25)|~v1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (k7_relat_1(esk8_0,esk6_0)=esk8_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (~r1_tarski(esk8_0,k7_relat_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_20, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(k4_tarski(X1,X2),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_15])])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),esk5_2(esk8_0,k7_relat_1(esk7_0,esk6_0))),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_15])])).
% 0.13/0.38  fof(c_0_24, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_12])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),esk6_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.38  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (r1_tarski(esk8_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),k7_relat_1(X2,esk6_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(X1,esk7_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),k7_relat_1(esk7_0,esk6_0))|~r2_hidden(k4_tarski(esk4_2(esk8_0,k7_relat_1(esk7_0,esk6_0)),X1),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_15]), c_0_23])]), c_0_19]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 35
% 0.13/0.38  # Proof object clause steps            : 22
% 0.13/0.38  # Proof object formula steps           : 13
% 0.13/0.38  # Proof object conjectures             : 16
% 0.13/0.38  # Proof object clause conjectures      : 13
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 6
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 16
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 6
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 19
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 19
% 0.13/0.38  # Processed clauses                    : 67
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 2
% 0.13/0.38  # ...remaining for further processing  : 65
% 0.13/0.38  # Other redundant clauses eliminated   : 3
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 94
% 0.13/0.38  # ...of the previous two non-trivial   : 77
% 0.13/0.38  # Contextual simplify-reflections      : 3
% 0.13/0.38  # Paramodulations                      : 91
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 3
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
% 0.13/0.38  # Current number of processed clauses  : 42
% 0.13/0.38  #    Positive orientable unit clauses  : 12
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 1
% 0.13/0.38  #    Non-unit-clauses                  : 29
% 0.13/0.38  # Current number of unprocessed clauses: 46
% 0.13/0.38  # ...number of literals in the above   : 171
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 20
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 242
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 158
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.13/0.38  # Unit Clause-clause subsumption calls : 16
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3410
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.035 s
% 0.13/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
