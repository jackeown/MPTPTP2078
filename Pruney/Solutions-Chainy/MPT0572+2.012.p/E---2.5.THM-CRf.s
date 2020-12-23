%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:47 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 107 expanded)
%              Number of clauses        :   24 (  46 expanded)
%              Number of leaves         :    5 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  141 ( 414 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t176_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))) ) ),
    inference(assume_negation,[status(cth)],[t176_relat_1])).

fof(c_0_6,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ~ r1_tarski(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24,X26,X27,X28,X29,X31] :
      ( ( r2_hidden(k4_tarski(X24,esk3_4(X21,X22,X23,X24)),X21)
        | ~ r2_hidden(X24,X23)
        | X23 != k10_relat_1(X21,X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk3_4(X21,X22,X23,X24),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k10_relat_1(X21,X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(X26,X27),X21)
        | ~ r2_hidden(X27,X22)
        | r2_hidden(X26,X23)
        | X23 != k10_relat_1(X21,X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(esk4_3(X21,X28,X29),X29)
        | ~ r2_hidden(k4_tarski(esk4_3(X21,X28,X29),X31),X21)
        | ~ r2_hidden(X31,X28)
        | X29 = k10_relat_1(X21,X28)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk4_3(X21,X28,X29),esk5_3(X21,X28,X29)),X21)
        | r2_hidden(esk4_3(X21,X28,X29),X29)
        | X29 = k10_relat_1(X21,X28)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk5_3(X21,X28,X29),X28)
        | r2_hidden(esk4_3(X21,X28,X29),X29)
        | X29 = k10_relat_1(X21,X28)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_9,plain,(
    ! [X33,X34,X35,X37] :
      ( ( r2_hidden(esk6_3(X33,X34,X35),k2_relat_1(X35))
        | ~ r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(k4_tarski(X33,esk6_3(X33,X34,X35)),X35)
        | ~ r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) )
      & ( r2_hidden(esk6_3(X33,X34,X35),X34)
        | ~ r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) )
      & ( ~ r2_hidden(X37,k2_relat_1(X35))
        | ~ r2_hidden(k4_tarski(X33,X37),X35)
        | ~ r2_hidden(X37,X34)
        | r2_hidden(X33,k10_relat_1(X35,X34))
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_10,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk2_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk2_3(X17,X18,X19),X18)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X17)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk2_3(X17,X18,X19),X18)
        | r2_hidden(esk2_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X1,X2,X3)),X3)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0)),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),k3_xboole_0(esk7_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_15]),c_0_16])])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,X1))
    | ~ r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_16])])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_10]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.13/0.40  # and selection function SelectCQIArNXTEqFirst.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.051 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t176_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.13/0.40  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.13/0.40  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.13/0.40  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>r1_tarski(k10_relat_1(X3,k3_xboole_0(X1,X2)),k3_xboole_0(k10_relat_1(X3,X1),k10_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t176_relat_1])).
% 0.13/0.40  fof(c_0_6, negated_conjecture, (v1_relat_1(esk9_0)&~r1_tarski(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.13/0.40  fof(c_0_7, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  fof(c_0_8, plain, ![X21, X22, X23, X24, X26, X27, X28, X29, X31]:((((r2_hidden(k4_tarski(X24,esk3_4(X21,X22,X23,X24)),X21)|~r2_hidden(X24,X23)|X23!=k10_relat_1(X21,X22)|~v1_relat_1(X21))&(r2_hidden(esk3_4(X21,X22,X23,X24),X22)|~r2_hidden(X24,X23)|X23!=k10_relat_1(X21,X22)|~v1_relat_1(X21)))&(~r2_hidden(k4_tarski(X26,X27),X21)|~r2_hidden(X27,X22)|r2_hidden(X26,X23)|X23!=k10_relat_1(X21,X22)|~v1_relat_1(X21)))&((~r2_hidden(esk4_3(X21,X28,X29),X29)|(~r2_hidden(k4_tarski(esk4_3(X21,X28,X29),X31),X21)|~r2_hidden(X31,X28))|X29=k10_relat_1(X21,X28)|~v1_relat_1(X21))&((r2_hidden(k4_tarski(esk4_3(X21,X28,X29),esk5_3(X21,X28,X29)),X21)|r2_hidden(esk4_3(X21,X28,X29),X29)|X29=k10_relat_1(X21,X28)|~v1_relat_1(X21))&(r2_hidden(esk5_3(X21,X28,X29),X28)|r2_hidden(esk4_3(X21,X28,X29),X29)|X29=k10_relat_1(X21,X28)|~v1_relat_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.13/0.40  fof(c_0_9, plain, ![X33, X34, X35, X37]:((((r2_hidden(esk6_3(X33,X34,X35),k2_relat_1(X35))|~r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35))&(r2_hidden(k4_tarski(X33,esk6_3(X33,X34,X35)),X35)|~r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35)))&(r2_hidden(esk6_3(X33,X34,X35),X34)|~r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35)))&(~r2_hidden(X37,k2_relat_1(X35))|~r2_hidden(k4_tarski(X33,X37),X35)|~r2_hidden(X37,X34)|r2_hidden(X33,k10_relat_1(X35,X34))|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.13/0.40  cnf(c_0_10, negated_conjecture, (~r1_tarski(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_11, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  fof(c_0_12, plain, ![X12, X13, X14, X15, X16, X17, X18, X19]:((((r2_hidden(X15,X12)|~r2_hidden(X15,X14)|X14!=k3_xboole_0(X12,X13))&(r2_hidden(X15,X13)|~r2_hidden(X15,X14)|X14!=k3_xboole_0(X12,X13)))&(~r2_hidden(X16,X12)|~r2_hidden(X16,X13)|r2_hidden(X16,X14)|X14!=k3_xboole_0(X12,X13)))&((~r2_hidden(esk2_3(X17,X18,X19),X19)|(~r2_hidden(esk2_3(X17,X18,X19),X17)|~r2_hidden(esk2_3(X17,X18,X19),X18))|X19=k3_xboole_0(X17,X18))&((r2_hidden(esk2_3(X17,X18,X19),X17)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k3_xboole_0(X17,X18))&(r2_hidden(esk2_3(X17,X18,X19),X18)|r2_hidden(esk2_3(X17,X18,X19),X19)|X19=k3_xboole_0(X17,X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_13, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,esk6_3(X1,X2,X3)),X3)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_15, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.40  cnf(c_0_16, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.40  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_18, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_20, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_21, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_13])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(k4_tarski(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0)),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.13/0.40  cnf(c_0_23, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),k3_xboole_0(esk7_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_15]), c_0_16])])).
% 0.13/0.40  cnf(c_0_25, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_26, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.40  cnf(c_0_27, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,X1))|~r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_16])])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (r2_hidden(esk6_3(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k3_xboole_0(esk7_0,esk8_0),esk9_0),esk7_0)), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.13/0.40  cnf(c_0_31, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X3)|~r2_hidden(esk1_2(X1,k3_xboole_0(X2,X3)),X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.40  cnf(c_0_32, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk1_2(k10_relat_1(esk9_0,k3_xboole_0(esk7_0,esk8_0)),k3_xboole_0(k10_relat_1(esk9_0,esk7_0),k10_relat_1(esk9_0,esk8_0))),k10_relat_1(esk9_0,esk7_0))), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_10]), c_0_33])]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 35
% 0.13/0.40  # Proof object clause steps            : 24
% 0.13/0.40  # Proof object formula steps           : 11
% 0.13/0.40  # Proof object conjectures             : 14
% 0.13/0.40  # Proof object clause conjectures      : 11
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 10
% 0.13/0.40  # Proof object initial formulas used   : 5
% 0.13/0.40  # Proof object generating inferences   : 10
% 0.13/0.40  # Proof object simplifying inferences  : 13
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 5
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 21
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 21
% 0.13/0.40  # Processed clauses                    : 74
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 3
% 0.13/0.40  # ...remaining for further processing  : 70
% 0.13/0.40  # Other redundant clauses eliminated   : 6
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 0
% 0.13/0.40  # Backward-rewritten                   : 0
% 0.13/0.40  # Generated clauses                    : 174
% 0.13/0.40  # ...of the previous two non-trivial   : 166
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 164
% 0.13/0.40  # Factorizations                       : 4
% 0.13/0.40  # Equation resolutions                 : 6
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 44
% 0.13/0.40  #    Positive orientable unit clauses  : 12
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 1
% 0.13/0.40  #    Non-unit-clauses                  : 31
% 0.13/0.40  # Current number of unprocessed clauses: 133
% 0.13/0.40  # ...number of literals in the above   : 400
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 20
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 414
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 318
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 3
% 0.13/0.40  # Unit Clause-clause subsumption calls : 14
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 0
% 0.13/0.40  # BW rewrite match successes           : 0
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 5723
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.058 s
% 0.13/0.40  # System time              : 0.008 s
% 0.13/0.40  # Total time               : 0.067 s
% 0.13/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
