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
% DateTime   : Thu Dec  3 11:00:40 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 126 expanded)
%              Number of clauses        :   37 (  59 expanded)
%              Number of leaves         :    6 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  198 ( 687 expanded)
%              Number of equality atoms :   19 (  62 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_wellord2,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k1_wellord2(X1)
      <=> ( k3_relat_1(X2) = X1
          & ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1) )
             => ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> r1_tarski(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d8_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r8_relat_2(X1,X2)
        <=> ! [X3,X4,X5] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(X5,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X5),X1) )
             => r2_hidden(k4_tarski(X3,X5),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d16_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> r8_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_2)).

fof(t3_wellord2,conjecture,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(c_0_6,plain,(
    ! [X13,X14,X15,X16] :
      ( ( k3_relat_1(X14) = X13
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(X15,X16),X14)
        | r1_tarski(X15,X16)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r1_tarski(X15,X16)
        | r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(X15,X13)
        | ~ r2_hidden(X16,X13)
        | X14 != k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk2_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_2(X13,X14),X13)
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | ~ r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)
        | r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))
        | k3_relat_1(X14) != X13
        | X14 = k1_wellord2(X13)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_7,plain,(
    ! [X28] : v1_relat_1(k1_wellord2(X28)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22,X23,X24] :
      ( ( ~ r8_relat_2(X19,X20)
        | ~ r2_hidden(X21,X20)
        | ~ r2_hidden(X22,X20)
        | ~ r2_hidden(X23,X20)
        | ~ r2_hidden(k4_tarski(X21,X22),X19)
        | ~ r2_hidden(k4_tarski(X22,X23),X19)
        | r2_hidden(k4_tarski(X21,X23),X19)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X24),X24)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk5_2(X19,X24),X24)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk6_2(X19,X24),X24)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk4_2(X19,X24),esk5_2(X19,X24)),X19)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk5_2(X19,X24),esk6_2(X19,X24)),X19)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X19,X24),esk6_2(X19,X24)),X19)
        | r8_relat_2(X19,X24)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_14,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r1_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk5_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_21,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk4_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( r8_relat_2(k1_wellord2(X1),X1)
    | r1_tarski(esk4_2(k1_wellord2(X1),X1),esk5_2(k1_wellord2(X1),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(k4_tarski(esk5_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_10])).

cnf(c_0_26,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r8_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( r8_relat_2(k1_wellord2(X1),X1)
    | r2_hidden(esk1_2(esk4_2(k1_wellord2(X1),X1),X2),esk5_2(k1_wellord2(X1),X1))
    | r1_tarski(esk4_2(k1_wellord2(X1),X1),X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r1_tarski(esk5_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk6_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk5_2(k1_wellord2(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_25])).

cnf(c_0_29,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk6_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_10])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( r8_relat_2(k1_wellord2(X1),X1)
    | r2_hidden(esk1_2(esk4_2(k1_wellord2(X1),X1),X2),X3)
    | r1_tarski(esk4_2(k1_wellord2(X1),X1),X2)
    | ~ r1_tarski(esk5_2(k1_wellord2(X1),X1),X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_27])).

cnf(c_0_32,plain,
    ( r8_relat_2(k1_wellord2(X1),X1)
    | r1_tarski(esk5_2(k1_wellord2(X1),X1),esk6_2(k1_wellord2(X1),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])).

fof(c_0_33,plain,(
    ! [X12] :
      ( ( ~ v8_relat_2(X12)
        | r8_relat_2(X12,k3_relat_1(X12))
        | ~ v1_relat_1(X12) )
      & ( ~ r8_relat_2(X12,k3_relat_1(X12))
        | v8_relat_2(X12)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).

cnf(c_0_34,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,plain,
    ( r8_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),esk6_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_10])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,plain,
    ( r8_relat_2(k1_wellord2(X1),X1)
    | r2_hidden(esk1_2(esk4_2(k1_wellord2(X1),X1),X2),esk6_2(k1_wellord2(X1),X1))
    | r1_tarski(esk4_2(k1_wellord2(X1),X1),X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_39,negated_conjecture,(
    ~ ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t3_wellord2])).

cnf(c_0_40,plain,
    ( v8_relat_2(X1)
    | ~ r8_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_10])])).

cnf(c_0_42,plain,
    ( r8_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(esk6_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)
    | ~ r1_tarski(esk4_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_10])])).

cnf(c_0_43,plain,
    ( r8_relat_2(k1_wellord2(X1),X1)
    | r1_tarski(esk4_2(k1_wellord2(X1),X1),esk6_2(k1_wellord2(X1),X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_44,negated_conjecture,(
    ~ v8_relat_2(k1_wellord2(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).

cnf(c_0_45,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | ~ r8_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_10])])).

cnf(c_0_46,plain,
    ( r8_relat_2(k1_wellord2(X1),X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21]),c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( ~ v8_relat_2(k1_wellord2(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.40  #
% 0.19/0.40  # Preprocessing time       : 0.046 s
% 0.19/0.40  # Presaturation interreduction done
% 0.19/0.40  
% 0.19/0.40  # Proof found!
% 0.19/0.40  # SZS status Theorem
% 0.19/0.40  # SZS output start CNFRefutation
% 0.19/0.40  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.19/0.40  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.19/0.40  fof(d8_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r8_relat_2(X1,X2)<=>![X3, X4, X5]:(((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(X5,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X5),X1))=>r2_hidden(k4_tarski(X3,X5),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_2)).
% 0.19/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.40  fof(d16_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>r8_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_2)).
% 0.19/0.40  fof(t3_wellord2, conjecture, ![X1]:v8_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_wellord2)).
% 0.19/0.40  fof(c_0_6, plain, ![X13, X14, X15, X16]:(((k3_relat_1(X14)=X13|X14!=k1_wellord2(X13)|~v1_relat_1(X14))&((~r2_hidden(k4_tarski(X15,X16),X14)|r1_tarski(X15,X16)|(~r2_hidden(X15,X13)|~r2_hidden(X16,X13))|X14!=k1_wellord2(X13)|~v1_relat_1(X14))&(~r1_tarski(X15,X16)|r2_hidden(k4_tarski(X15,X16),X14)|(~r2_hidden(X15,X13)|~r2_hidden(X16,X13))|X14!=k1_wellord2(X13)|~v1_relat_1(X14))))&(((r2_hidden(esk2_2(X13,X14),X13)|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))&(r2_hidden(esk3_2(X13,X14),X13)|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14)))&((~r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)|~r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk2_2(X13,X14),esk3_2(X13,X14)),X14)|r1_tarski(esk2_2(X13,X14),esk3_2(X13,X14))|k3_relat_1(X14)!=X13|X14=k1_wellord2(X13)|~v1_relat_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.19/0.40  fof(c_0_7, plain, ![X28]:v1_relat_1(k1_wellord2(X28)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.19/0.40  fof(c_0_8, plain, ![X19, X20, X21, X22, X23, X24]:((~r8_relat_2(X19,X20)|(~r2_hidden(X21,X20)|~r2_hidden(X22,X20)|~r2_hidden(X23,X20)|~r2_hidden(k4_tarski(X21,X22),X19)|~r2_hidden(k4_tarski(X22,X23),X19)|r2_hidden(k4_tarski(X21,X23),X19))|~v1_relat_1(X19))&((((((r2_hidden(esk4_2(X19,X24),X24)|r8_relat_2(X19,X24)|~v1_relat_1(X19))&(r2_hidden(esk5_2(X19,X24),X24)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(r2_hidden(esk6_2(X19,X24),X24)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(r2_hidden(k4_tarski(esk4_2(X19,X24),esk5_2(X19,X24)),X19)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(r2_hidden(k4_tarski(esk5_2(X19,X24),esk6_2(X19,X24)),X19)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))&(~r2_hidden(k4_tarski(esk4_2(X19,X24),esk6_2(X19,X24)),X19)|r8_relat_2(X19,X24)|~v1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_relat_2])])])])])])).
% 0.19/0.40  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_10, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.40  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  fof(c_0_12, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.40  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])])).
% 0.19/0.40  cnf(c_0_14, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.19/0.40  cnf(c_0_15, plain, (r2_hidden(esk5_2(X1,X2),X2)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_16, plain, (r2_hidden(esk4_2(X1,X2),X2)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_17, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_18, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_19, plain, (r8_relat_2(k1_wellord2(X1),X2)|r1_tarski(esk4_2(k1_wellord2(X1),X2),esk5_2(k1_wellord2(X1),X2))|~r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)|~r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.40  cnf(c_0_20, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(esk5_2(k1_wellord2(X1),X2),X2)), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 0.19/0.40  cnf(c_0_21, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(esk4_2(k1_wellord2(X1),X2),X2)), inference(spm,[status(thm)],[c_0_16, c_0_10])).
% 0.19/0.40  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk5_2(X1,X2),esk6_2(X1,X2)),X1)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.40  cnf(c_0_24, plain, (r8_relat_2(k1_wellord2(X1),X1)|r1_tarski(esk4_2(k1_wellord2(X1),X1),esk5_2(k1_wellord2(X1),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])).
% 0.19/0.40  cnf(c_0_25, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(k4_tarski(esk5_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2)),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_22, c_0_10])).
% 0.19/0.40  cnf(c_0_26, plain, (r2_hidden(esk6_2(X1,X2),X2)|r8_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_27, plain, (r8_relat_2(k1_wellord2(X1),X1)|r2_hidden(esk1_2(esk4_2(k1_wellord2(X1),X1),X2),esk5_2(k1_wellord2(X1),X1))|r1_tarski(esk4_2(k1_wellord2(X1),X1),X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.40  cnf(c_0_28, plain, (r8_relat_2(k1_wellord2(X1),X2)|r1_tarski(esk5_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2))|~r2_hidden(esk6_2(k1_wellord2(X1),X2),X1)|~r2_hidden(esk5_2(k1_wellord2(X1),X2),X1)), inference(spm,[status(thm)],[c_0_13, c_0_25])).
% 0.19/0.40  cnf(c_0_29, plain, (r8_relat_2(k1_wellord2(X1),X2)|r2_hidden(esk6_2(k1_wellord2(X1),X2),X2)), inference(spm,[status(thm)],[c_0_26, c_0_10])).
% 0.19/0.40  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_31, plain, (r8_relat_2(k1_wellord2(X1),X1)|r2_hidden(esk1_2(esk4_2(k1_wellord2(X1),X1),X2),X3)|r1_tarski(esk4_2(k1_wellord2(X1),X1),X2)|~r1_tarski(esk5_2(k1_wellord2(X1),X1),X3)), inference(spm,[status(thm)],[c_0_17, c_0_27])).
% 0.19/0.40  cnf(c_0_32, plain, (r8_relat_2(k1_wellord2(X1),X1)|r1_tarski(esk5_2(k1_wellord2(X1),X1),esk6_2(k1_wellord2(X1),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_20])).
% 0.19/0.40  fof(c_0_33, plain, ![X12]:((~v8_relat_2(X12)|r8_relat_2(X12,k3_relat_1(X12))|~v1_relat_1(X12))&(~r8_relat_2(X12,k3_relat_1(X12))|v8_relat_2(X12)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_2])])])).
% 0.19/0.40  cnf(c_0_34, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.40  cnf(c_0_35, plain, (r8_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),esk6_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.40  cnf(c_0_36, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_10])])).
% 0.19/0.40  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.40  cnf(c_0_38, plain, (r8_relat_2(k1_wellord2(X1),X1)|r2_hidden(esk1_2(esk4_2(k1_wellord2(X1),X1),X2),esk6_2(k1_wellord2(X1),X1))|r1_tarski(esk4_2(k1_wellord2(X1),X1),X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.40  fof(c_0_39, negated_conjecture, ~(![X1]:v8_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t3_wellord2])).
% 0.19/0.40  cnf(c_0_40, plain, (v8_relat_2(X1)|~r8_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.40  cnf(c_0_41, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_10])])).
% 0.19/0.40  cnf(c_0_42, plain, (r8_relat_2(k1_wellord2(X1),X2)|~r2_hidden(esk6_2(k1_wellord2(X1),X2),X1)|~r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)|~r1_tarski(esk4_2(k1_wellord2(X1),X2),esk6_2(k1_wellord2(X1),X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_10])])).
% 0.19/0.40  cnf(c_0_43, plain, (r8_relat_2(k1_wellord2(X1),X1)|r1_tarski(esk4_2(k1_wellord2(X1),X1),esk6_2(k1_wellord2(X1),X1))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.40  fof(c_0_44, negated_conjecture, ~v8_relat_2(k1_wellord2(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_39])])])).
% 0.19/0.40  cnf(c_0_45, plain, (v8_relat_2(k1_wellord2(X1))|~r8_relat_2(k1_wellord2(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_10])])).
% 0.19/0.40  cnf(c_0_46, plain, (r8_relat_2(k1_wellord2(X1),X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21]), c_0_29])).
% 0.19/0.40  cnf(c_0_47, negated_conjecture, (~v8_relat_2(k1_wellord2(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.40  cnf(c_0_48, plain, (v8_relat_2(k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46])])).
% 0.19/0.40  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), ['proof']).
% 0.19/0.40  # SZS output end CNFRefutation
% 0.19/0.40  # Proof object total steps             : 50
% 0.19/0.40  # Proof object clause steps            : 37
% 0.19/0.40  # Proof object formula steps           : 13
% 0.19/0.40  # Proof object conjectures             : 5
% 0.19/0.40  # Proof object clause conjectures      : 2
% 0.19/0.40  # Proof object formula conjectures     : 3
% 0.19/0.40  # Proof object initial clauses used    : 15
% 0.19/0.40  # Proof object initial formulas used   : 6
% 0.19/0.40  # Proof object generating inferences   : 17
% 0.19/0.40  # Proof object simplifying inferences  : 21
% 0.19/0.40  # Training examples: 0 positive, 0 negative
% 0.19/0.40  # Parsed axioms                        : 6
% 0.19/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.40  # Initial clauses                      : 21
% 0.19/0.40  # Removed in clause preprocessing      : 0
% 0.19/0.40  # Initial clauses in saturation        : 21
% 0.19/0.40  # Processed clauses                    : 91
% 0.19/0.40  # ...of these trivial                  : 0
% 0.19/0.40  # ...subsumed                          : 10
% 0.19/0.40  # ...remaining for further processing  : 81
% 0.19/0.40  # Other redundant clauses eliminated   : 7
% 0.19/0.40  # Clauses deleted for lack of memory   : 0
% 0.19/0.40  # Backward-subsumed                    : 0
% 0.19/0.40  # Backward-rewritten                   : 12
% 0.19/0.40  # Generated clauses                    : 71
% 0.19/0.40  # ...of the previous two non-trivial   : 67
% 0.19/0.40  # Contextual simplify-reflections      : 4
% 0.19/0.40  # Paramodulations                      : 64
% 0.19/0.40  # Factorizations                       : 0
% 0.19/0.40  # Equation resolutions                 : 7
% 0.19/0.40  # Propositional unsat checks           : 0
% 0.19/0.40  #    Propositional check models        : 0
% 0.19/0.40  #    Propositional check unsatisfiable : 0
% 0.19/0.40  #    Propositional clauses             : 0
% 0.19/0.40  #    Propositional clauses after purity: 0
% 0.19/0.40  #    Propositional unsat core size     : 0
% 0.19/0.40  #    Propositional preprocessing time  : 0.000
% 0.19/0.40  #    Propositional encoding time       : 0.000
% 0.19/0.40  #    Propositional solver time         : 0.000
% 0.19/0.40  #    Success case prop preproc time    : 0.000
% 0.19/0.40  #    Success case prop encoding time   : 0.000
% 0.19/0.40  #    Success case prop solver time     : 0.000
% 0.19/0.40  # Current number of processed clauses  : 41
% 0.19/0.40  #    Positive orientable unit clauses  : 5
% 0.19/0.40  #    Positive unorientable unit clauses: 0
% 0.19/0.40  #    Negative unit clauses             : 0
% 0.19/0.40  #    Non-unit-clauses                  : 36
% 0.19/0.40  # Current number of unprocessed clauses: 17
% 0.19/0.40  # ...number of literals in the above   : 77
% 0.19/0.40  # Current number of archived formulas  : 0
% 0.19/0.40  # Current number of archived clauses   : 33
% 0.19/0.40  # Clause-clause subsumption calls (NU) : 792
% 0.19/0.40  # Rec. Clause-clause subsumption calls : 392
% 0.19/0.40  # Non-unit clause-clause subsumptions  : 14
% 0.19/0.40  # Unit Clause-clause subsumption calls : 36
% 0.19/0.40  # Rewrite failures with RHS unbound    : 0
% 0.19/0.40  # BW rewrite match attempts            : 7
% 0.19/0.40  # BW rewrite match successes           : 3
% 0.19/0.40  # Condensation attempts                : 0
% 0.19/0.40  # Condensation successes               : 0
% 0.19/0.40  # Termbank termtop insertions          : 3806
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.056 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.060 s
% 0.19/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
