%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:10 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   28 (  45 expanded)
%              Number of clauses        :   15 (  18 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :  109 ( 146 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t167_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

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

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)) ) ),
    inference(assume_negation,[status(cth)],[t167_relat_1])).

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
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | v1_relat_1(k7_relat_1(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

fof(c_0_9,plain,(
    ! [X28] :
      ( ~ v1_relat_1(X28)
      | k7_relat_1(X28,k1_relat_1(X28)) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

fof(c_0_10,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ~ r1_tarski(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

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

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k7_relat_1(X5,X2)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X27] :
      ( ( r2_hidden(esk4_3(X23,X24,X25),k2_relat_1(X25))
        | ~ r2_hidden(X23,k10_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(X23,esk4_3(X23,X24,X25)),X25)
        | ~ r2_hidden(X23,k10_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(esk4_3(X23,X24,X25),X24)
        | ~ r2_hidden(X23,k10_relat_1(X25,X24))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X27,k2_relat_1(X25))
        | ~ r2_hidden(k4_tarski(X23,X27),X25)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X23,k10_relat_1(X25,X24))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_17,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( k7_relat_1(esk6_0,k1_relat_1(esk6_0)) = esk6_0 ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),k10_relat_1(esk6_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(k4_tarski(X1,X2),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_15])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),esk4_3(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),esk5_0,esk6_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_15])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_17]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.13/0.37  # and selection function SelectCQIArNXTEqFirst.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t167_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 0.13/0.37  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 0.13/0.37  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.37  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 0.13/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.37  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.13/0.37  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k10_relat_1(X2,X1),k1_relat_1(X2)))), inference(assume_negation,[status(cth)],[t167_relat_1])).
% 0.13/0.37  fof(c_0_7, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X15,X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(X15,X16),X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&(~r2_hidden(X17,X13)|~r2_hidden(k4_tarski(X17,X18),X12)|r2_hidden(k4_tarski(X17,X18),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|(~r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12))|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&((r2_hidden(esk2_3(X12,X13,X14),X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.13/0.37  fof(c_0_8, plain, ![X21, X22]:(~v1_relat_1(X21)|v1_relat_1(k7_relat_1(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.37  fof(c_0_9, plain, ![X28]:(~v1_relat_1(X28)|k7_relat_1(X28,k1_relat_1(X28))=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.13/0.37  fof(c_0_10, negated_conjecture, (v1_relat_1(esk6_0)&~r1_tarski(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.37  fof(c_0_11, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.37  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k7_relat_1(X5,X2)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_13, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.37  cnf(c_0_14, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  fof(c_0_16, plain, ![X23, X24, X25, X27]:((((r2_hidden(esk4_3(X23,X24,X25),k2_relat_1(X25))|~r2_hidden(X23,k10_relat_1(X25,X24))|~v1_relat_1(X25))&(r2_hidden(k4_tarski(X23,esk4_3(X23,X24,X25)),X25)|~r2_hidden(X23,k10_relat_1(X25,X24))|~v1_relat_1(X25)))&(r2_hidden(esk4_3(X23,X24,X25),X24)|~r2_hidden(X23,k10_relat_1(X25,X24))|~v1_relat_1(X25)))&(~r2_hidden(X27,k2_relat_1(X25))|~r2_hidden(k4_tarski(X23,X27),X25)|~r2_hidden(X27,X24)|r2_hidden(X23,k10_relat_1(X25,X24))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (~r1_tarski(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.37  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X4),k7_relat_1(X3,X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (k7_relat_1(esk6_0,k1_relat_1(esk6_0))=esk6_0), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.37  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,esk4_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),k10_relat_1(esk6_0,esk5_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,k1_relat_1(esk6_0))|~r2_hidden(k4_tarski(X1,X2),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_15])])).
% 0.13/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),esk4_3(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),esk5_0,esk6_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_15])])).
% 0.13/0.37  cnf(c_0_25, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk6_0,esk5_0),k1_relat_1(esk6_0)),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_17]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 28
% 0.13/0.37  # Proof object clause steps            : 15
% 0.13/0.37  # Proof object formula steps           : 13
% 0.13/0.37  # Proof object conjectures             : 11
% 0.13/0.37  # Proof object clause conjectures      : 8
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 8
% 0.13/0.37  # Proof object initial formulas used   : 6
% 0.13/0.37  # Proof object generating inferences   : 6
% 0.13/0.37  # Proof object simplifying inferences  : 7
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 6
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 17
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 17
% 0.13/0.37  # Processed clauses                    : 40
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 40
% 0.13/0.37  # Other redundant clauses eliminated   : 3
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 0
% 0.13/0.37  # Generated clauses                    : 16
% 0.13/0.37  # ...of the previous two non-trivial   : 13
% 0.13/0.37  # Contextual simplify-reflections      : 3
% 0.13/0.37  # Paramodulations                      : 13
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 3
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 20
% 0.13/0.37  #    Positive orientable unit clauses  : 7
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 1
% 0.13/0.37  #    Non-unit-clauses                  : 12
% 0.13/0.37  # Current number of unprocessed clauses: 7
% 0.13/0.37  # ...number of literals in the above   : 28
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 17
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 147
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 41
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.37  # Unit Clause-clause subsumption calls : 19
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 0
% 0.13/0.37  # BW rewrite match successes           : 0
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 1791
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.003 s
% 0.13/0.37  # Total time               : 0.033 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
