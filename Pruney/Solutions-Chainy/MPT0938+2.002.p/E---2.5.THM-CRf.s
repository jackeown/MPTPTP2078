%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:41 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 192 expanded)
%              Number of clauses        :   30 (  85 expanded)
%              Number of leaves         :    6 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  163 ( 865 expanded)
%              Number of equality atoms :   19 ( 147 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l2_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
      <=> ! [X2,X3,X4] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X4),X1) )
           => r2_hidden(k4_tarski(X2,X4),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

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

fof(t30_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_wellord2,conjecture,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(c_0_6,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v8_relat_2(X14)
        | ~ r2_hidden(k4_tarski(X15,X16),X14)
        | ~ r2_hidden(k4_tarski(X16,X17),X14)
        | r2_hidden(k4_tarski(X15,X17),X14)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk2_1(X14),esk3_1(X14)),X14)
        | v8_relat_2(X14)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk3_1(X14),esk4_1(X14)),X14)
        | v8_relat_2(X14)
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X14),esk4_1(X14)),X14)
        | v8_relat_2(X14)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

fof(c_0_7,plain,(
    ! [X27] : v1_relat_1(k1_wellord2(X27)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X21,X22,X23,X24] :
      ( ( k3_relat_1(X22) = X21
        | X22 != k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(X23,X24),X22)
        | r1_tarski(X23,X24)
        | ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X24,X21)
        | X22 != k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r1_tarski(X23,X24)
        | r2_hidden(k4_tarski(X23,X24),X22)
        | ~ r2_hidden(X23,X21)
        | ~ r2_hidden(X24,X21)
        | X22 != k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk5_2(X21,X22),X21)
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk6_2(X21,X22),X21)
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk5_2(X21,X22),esk6_2(X21,X22)),X22)
        | ~ r1_tarski(esk5_2(X21,X22),esk6_2(X21,X22))
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk5_2(X21,X22),esk6_2(X21,X22)),X22)
        | r1_tarski(esk5_2(X21,X22),esk6_2(X21,X22))
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] :
      ( ( r2_hidden(X11,k3_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) )
      & ( r2_hidden(X12,k3_relat_1(X13))
        | ~ r2_hidden(k4_tarski(X11,X12),X13)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_11])])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_11])])).

cnf(c_0_22,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk2_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_23,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk3_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(esk3_1(X1),esk4_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X3)
    | r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r1_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(k4_tarski(esk3_1(k1_wellord2(X1)),esk4_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_28,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk1_2(esk2_1(k1_wellord2(X1)),X2),esk3_1(k1_wellord2(X1)))
    | r1_tarski(esk2_1(k1_wellord2(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk4_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_27]),c_0_17]),c_0_11])])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t3_wellord2])).

cnf(c_0_32,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk1_2(esk2_1(k1_wellord2(X1)),X2),X3)
    | r1_tarski(esk2_1(k1_wellord2(X1)),X2)
    | ~ r1_tarski(esk3_1(k1_wellord2(X1)),X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_28])).

cnf(c_0_33,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r1_tarski(esk3_1(k1_wellord2(X1)),esk4_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_27]),c_0_23]),c_0_29])).

cnf(c_0_34,plain,
    ( v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk2_1(X1),esk4_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_11])])).

fof(c_0_36,negated_conjecture,(
    ~ v8_relat_2(k1_wellord2(esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).

cnf(c_0_37,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_38,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk1_2(esk2_1(k1_wellord2(X1)),X2),esk4_1(k1_wellord2(X1)))
    | r1_tarski(esk2_1(k1_wellord2(X1)),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk2_1(k1_wellord2(X1)),esk4_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_11])]),c_0_22]),c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( ~ v8_relat_2(k1_wellord2(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.20/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.38  fof(t3_wellord2, conjecture, ![X1]:v8_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_wellord2)).
% 0.20/0.38  fof(c_0_6, plain, ![X14, X15, X16, X17]:((~v8_relat_2(X14)|(~r2_hidden(k4_tarski(X15,X16),X14)|~r2_hidden(k4_tarski(X16,X17),X14)|r2_hidden(k4_tarski(X15,X17),X14))|~v1_relat_1(X14))&(((r2_hidden(k4_tarski(esk2_1(X14),esk3_1(X14)),X14)|v8_relat_2(X14)|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk3_1(X14),esk4_1(X14)),X14)|v8_relat_2(X14)|~v1_relat_1(X14)))&(~r2_hidden(k4_tarski(esk2_1(X14),esk4_1(X14)),X14)|v8_relat_2(X14)|~v1_relat_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.20/0.38  fof(c_0_7, plain, ![X27]:v1_relat_1(k1_wellord2(X27)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_8, plain, ![X21, X22, X23, X24]:(((k3_relat_1(X22)=X21|X22!=k1_wellord2(X21)|~v1_relat_1(X22))&((~r2_hidden(k4_tarski(X23,X24),X22)|r1_tarski(X23,X24)|(~r2_hidden(X23,X21)|~r2_hidden(X24,X21))|X22!=k1_wellord2(X21)|~v1_relat_1(X22))&(~r1_tarski(X23,X24)|r2_hidden(k4_tarski(X23,X24),X22)|(~r2_hidden(X23,X21)|~r2_hidden(X24,X21))|X22!=k1_wellord2(X21)|~v1_relat_1(X22))))&(((r2_hidden(esk5_2(X21,X22),X21)|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22))&(r2_hidden(esk6_2(X21,X22),X21)|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22)))&((~r2_hidden(k4_tarski(esk5_2(X21,X22),esk6_2(X21,X22)),X22)|~r1_tarski(esk5_2(X21,X22),esk6_2(X21,X22))|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk5_2(X21,X22),esk6_2(X21,X22)),X22)|r1_tarski(esk5_2(X21,X22),esk6_2(X21,X22))|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X11, X12, X13]:((r2_hidden(X11,k3_relat_1(X13))|~r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))&(r2_hidden(X12,k3_relat_1(X13))|~r2_hidden(k4_tarski(X11,X12),X13)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.20/0.38  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)|v8_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_13, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.38  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_15, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_16, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.38  cnf(c_0_17, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_11])])).
% 0.20/0.38  cnf(c_0_18, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_11])])).
% 0.20/0.38  cnf(c_0_22, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk2_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_11])])).
% 0.20/0.38  cnf(c_0_23, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk3_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_16]), c_0_17]), c_0_11])])).
% 0.20/0.38  cnf(c_0_24, plain, (r2_hidden(k4_tarski(esk3_1(X1),esk4_1(X1)),X1)|v8_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X3)|r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.38  cnf(c_0_26, plain, (v8_relat_2(k1_wellord2(X1))|r1_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_16]), c_0_22]), c_0_23])).
% 0.20/0.38  cnf(c_0_27, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(k4_tarski(esk3_1(k1_wellord2(X1)),esk4_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_24, c_0_11])).
% 0.20/0.38  cnf(c_0_28, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk1_2(esk2_1(k1_wellord2(X1)),X2),esk3_1(k1_wellord2(X1)))|r1_tarski(esk2_1(k1_wellord2(X1)),X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.38  cnf(c_0_29, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk4_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_27]), c_0_17]), c_0_11])])).
% 0.20/0.38  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_31, negated_conjecture, ~(![X1]:v8_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t3_wellord2])).
% 0.20/0.38  cnf(c_0_32, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk1_2(esk2_1(k1_wellord2(X1)),X2),X3)|r1_tarski(esk2_1(k1_wellord2(X1)),X2)|~r1_tarski(esk3_1(k1_wellord2(X1)),X3)), inference(spm,[status(thm)],[c_0_19, c_0_28])).
% 0.20/0.38  cnf(c_0_33, plain, (v8_relat_2(k1_wellord2(X1))|r1_tarski(esk3_1(k1_wellord2(X1)),esk4_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_27]), c_0_23]), c_0_29])).
% 0.20/0.38  cnf(c_0_34, plain, (v8_relat_2(X1)|~r2_hidden(k4_tarski(esk2_1(X1),esk4_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_11])])).
% 0.20/0.38  fof(c_0_36, negated_conjecture, ~v8_relat_2(k1_wellord2(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_31])])])).
% 0.20/0.38  cnf(c_0_37, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_38, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk1_2(esk2_1(k1_wellord2(X1)),X2),esk4_1(k1_wellord2(X1)))|r1_tarski(esk2_1(k1_wellord2(X1)),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.38  cnf(c_0_39, plain, (v8_relat_2(k1_wellord2(X1))|~r1_tarski(esk2_1(k1_wellord2(X1)),esk4_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_11])]), c_0_22]), c_0_29])).
% 0.20/0.38  cnf(c_0_40, negated_conjecture, (~v8_relat_2(k1_wellord2(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.38  cnf(c_0_41, plain, (v8_relat_2(k1_wellord2(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 43
% 0.20/0.38  # Proof object clause steps            : 30
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 5
% 0.20/0.38  # Proof object clause conjectures      : 2
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 13
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 13
% 0.20/0.38  # Proof object simplifying inferences  : 29
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 18
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 18
% 0.20/0.38  # Processed clauses                    : 100
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 15
% 0.20/0.38  # ...remaining for further processing  : 85
% 0.20/0.38  # Other redundant clauses eliminated   : 7
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 39
% 0.20/0.38  # Generated clauses                    : 82
% 0.20/0.38  # ...of the previous two non-trivial   : 73
% 0.20/0.38  # Contextual simplify-reflections      : 7
% 0.20/0.38  # Paramodulations                      : 75
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 7
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 21
% 0.20/0.38  #    Positive orientable unit clauses  : 4
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 17
% 0.20/0.38  # Current number of unprocessed clauses: 7
% 0.20/0.38  # ...number of literals in the above   : 22
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 57
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 1086
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 538
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 22
% 0.20/0.38  # Unit Clause-clause subsumption calls : 2
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 7
% 0.20/0.38  # BW rewrite match successes           : 5
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 4039
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.036 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
