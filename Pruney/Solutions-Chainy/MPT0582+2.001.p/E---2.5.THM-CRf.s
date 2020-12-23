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
% DateTime   : Thu Dec  3 10:51:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   34 (  71 expanded)
%              Number of clauses        :   21 (  28 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 309 expanded)
%              Number of equality atoms :   14 (  14 expanded)
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

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

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
    ! [X28,X29,X30,X32,X33,X34,X35,X37] :
      ( ( ~ r2_hidden(X30,X29)
        | r2_hidden(k4_tarski(X30,esk6_3(X28,X29,X30)),X28)
        | X29 != k1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(X32,X33),X28)
        | r2_hidden(X32,X29)
        | X29 != k1_relat_1(X28) )
      & ( ~ r2_hidden(esk7_2(X34,X35),X35)
        | ~ r2_hidden(k4_tarski(esk7_2(X34,X35),X37),X34)
        | X35 = k1_relat_1(X34) )
      & ( r2_hidden(esk7_2(X34,X35),X35)
        | r2_hidden(k4_tarski(esk7_2(X34,X35),esk8_2(X34,X35)),X34)
        | X35 = k1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_relat_1(esk11_0)
    & r1_tarski(k1_relat_1(esk11_0),esk9_0)
    & r1_tarski(esk11_0,esk10_0)
    & ~ r1_tarski(esk11_0,k7_relat_1(esk10_0,esk9_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
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

fof(c_0_10,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(esk11_0,k7_relat_1(esk10_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r1_tarski(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
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

fof(c_0_16,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X39)
      | v1_relat_1(k7_relat_1(X39,X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk11_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),esk5_2(esk11_0,k7_relat_1(esk10_0,esk9_0))),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X1,X3),X5)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X5 != k7_relat_1(X4,X2)
    | ~ v1_relat_1(X5)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk11_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),k7_relat_1(X2,esk9_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),k7_relat_1(esk10_0,esk9_0))
    | ~ r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_33,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_14]),c_0_20])]),c_0_12]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.39  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t186_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_relat_1)).
% 0.13/0.39  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.13/0.39  fof(d3_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_tarski(X1,X2)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X1)=>r2_hidden(k4_tarski(X3,X4),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 0.13/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.39  fof(d11_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(v1_relat_1(X3)=>(X3=k7_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X4,X2)&r2_hidden(k4_tarski(X4,X5),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 0.13/0.39  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.13/0.39  fof(c_0_6, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(X3,X2))=>r1_tarski(X3,k7_relat_1(X2,X1)))))), inference(assume_negation,[status(cth)],[t186_relat_1])).
% 0.13/0.39  fof(c_0_7, plain, ![X28, X29, X30, X32, X33, X34, X35, X37]:(((~r2_hidden(X30,X29)|r2_hidden(k4_tarski(X30,esk6_3(X28,X29,X30)),X28)|X29!=k1_relat_1(X28))&(~r2_hidden(k4_tarski(X32,X33),X28)|r2_hidden(X32,X29)|X29!=k1_relat_1(X28)))&((~r2_hidden(esk7_2(X34,X35),X35)|~r2_hidden(k4_tarski(esk7_2(X34,X35),X37),X34)|X35=k1_relat_1(X34))&(r2_hidden(esk7_2(X34,X35),X35)|r2_hidden(k4_tarski(esk7_2(X34,X35),esk8_2(X34,X35)),X34)|X35=k1_relat_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.13/0.39  fof(c_0_8, negated_conjecture, (v1_relat_1(esk10_0)&(v1_relat_1(esk11_0)&((r1_tarski(k1_relat_1(esk11_0),esk9_0)&r1_tarski(esk11_0,esk10_0))&~r1_tarski(esk11_0,k7_relat_1(esk10_0,esk9_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.39  fof(c_0_9, plain, ![X21, X22, X23, X24, X25]:((~r1_tarski(X21,X22)|(~r2_hidden(k4_tarski(X23,X24),X21)|r2_hidden(k4_tarski(X23,X24),X22))|~v1_relat_1(X21))&((r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X21)|r1_tarski(X21,X25)|~v1_relat_1(X21))&(~r2_hidden(k4_tarski(esk4_2(X21,X25),esk5_2(X21,X25)),X25)|r1_tarski(X21,X25)|~v1_relat_1(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_relat_1])])])])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.39  cnf(c_0_11, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.39  cnf(c_0_12, negated_conjecture, (~r1_tarski(esk11_0,k7_relat_1(esk10_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_13, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|r1_tarski(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_14, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  fof(c_0_15, plain, ![X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X15,X13)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(X15,X16),X12)|~r2_hidden(k4_tarski(X15,X16),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&(~r2_hidden(X17,X13)|~r2_hidden(k4_tarski(X17,X18),X12)|r2_hidden(k4_tarski(X17,X18),X14)|X14!=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12)))&((~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|(~r2_hidden(esk2_3(X12,X13,X14),X13)|~r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12))|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&((r2_hidden(esk2_3(X12,X13,X14),X13)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))&(r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X12)|r2_hidden(k4_tarski(esk2_3(X12,X13,X14),esk3_3(X12,X13,X14)),X14)|X14=k7_relat_1(X12,X13)|~v1_relat_1(X14)|~v1_relat_1(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_relat_1])])])])])])).
% 0.13/0.39  fof(c_0_16, plain, ![X39, X40]:(~v1_relat_1(X39)|v1_relat_1(k7_relat_1(X39,X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.13/0.39  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_18, negated_conjecture, (r1_tarski(k1_relat_1(esk11_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_19, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_20, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),esk5_2(esk11_0,k7_relat_1(esk10_0,esk9_0))),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.13/0.39  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X1,X3),X5)|~r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X5!=k7_relat_1(X4,X2)|~v1_relat_1(X5)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_22, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.39  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.39  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,X2),k7_relat_1(X3,X4))|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_21]), c_0_22])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),esk9_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(esk11_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),k7_relat_1(X2,esk9_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_17, c_0_27])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.39  cnf(c_0_31, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),k7_relat_1(esk10_0,esk9_0))|~r2_hidden(k4_tarski(esk4_2(esk11_0,k7_relat_1(esk10_0,esk9_0)),X1),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_14]), c_0_20])]), c_0_12]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 34
% 0.13/0.39  # Proof object clause steps            : 21
% 0.13/0.39  # Proof object formula steps           : 13
% 0.13/0.39  # Proof object conjectures             : 16
% 0.13/0.39  # Proof object clause conjectures      : 13
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 11
% 0.13/0.39  # Proof object initial formulas used   : 6
% 0.13/0.39  # Proof object generating inferences   : 8
% 0.13/0.39  # Proof object simplifying inferences  : 11
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 6
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 22
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 22
% 0.13/0.39  # Processed clauses                    : 131
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 17
% 0.13/0.39  # ...remaining for further processing  : 114
% 0.13/0.39  # Other redundant clauses eliminated   : 5
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 0
% 0.13/0.39  # Generated clauses                    : 359
% 0.13/0.39  # ...of the previous two non-trivial   : 338
% 0.13/0.39  # Contextual simplify-reflections      : 4
% 0.13/0.39  # Paramodulations                      : 354
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 5
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 88
% 0.13/0.39  #    Positive orientable unit clauses  : 15
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 1
% 0.13/0.39  #    Non-unit-clauses                  : 72
% 0.13/0.39  # Current number of unprocessed clauses: 247
% 0.13/0.39  # ...number of literals in the above   : 772
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 21
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1297
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 969
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 21
% 0.13/0.39  # Unit Clause-clause subsumption calls : 54
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 4
% 0.13/0.39  # BW rewrite match successes           : 0
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 8973
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.007 s
% 0.13/0.39  # Total time               : 0.044 s
% 0.13/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
