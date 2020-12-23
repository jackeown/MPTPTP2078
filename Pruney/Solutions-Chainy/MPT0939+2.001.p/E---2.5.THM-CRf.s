%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 246 expanded)
%              Number of clauses        :   31 ( 104 expanded)
%              Number of leaves         :    9 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :  193 (1147 expanded)
%              Number of equality atoms :   21 ( 216 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(l4_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
      <=> ! [X2,X3] :
            ~ ( r2_hidden(X2,k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X1))
              & X2 != X3
              & ~ r2_hidden(k4_tarski(X2,X3),X1)
              & ~ r2_hidden(k4_tarski(X3,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(t23_ordinal1,axiom,(
    ! [X1,X2] :
      ( v3_ordinal1(X2)
     => ( r2_hidden(X1,X2)
       => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(t4_wellord2,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v6_relat_2(k1_wellord2(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(c_0_9,plain,(
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
      & ( r2_hidden(esk4_2(X21,X22),X21)
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(esk5_2(X21,X22),X21)
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X22)
        | ~ r1_tarski(esk4_2(X21,X22),esk5_2(X21,X22))
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) )
      & ( r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X22)
        | r1_tarski(esk4_2(X21,X22),esk5_2(X21,X22))
        | k3_relat_1(X22) != X21
        | X22 = k1_wellord2(X21)
        | ~ v1_relat_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_10,plain,(
    ! [X27] : v1_relat_1(k1_wellord2(X27)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v6_relat_2(X16)
        | ~ r2_hidden(X17,k3_relat_1(X16))
        | ~ r2_hidden(X18,k3_relat_1(X16))
        | X17 = X18
        | r2_hidden(k4_tarski(X17,X18),X16)
        | r2_hidden(k4_tarski(X18,X17),X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk2_1(X16),k3_relat_1(X16))
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_1(X16),k3_relat_1(X16))
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( esk2_1(X16) != esk3_1(X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X16),esk3_1(X16)),X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_1(X16),esk2_1(X16)),X16)
        | v6_relat_2(X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_12,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X12,X13] :
      ( ~ v3_ordinal1(X13)
      | ~ r2_hidden(X12,X13)
      | v3_ordinal1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_1(X1),k3_relat_1(X1))
    | v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v6_relat_2(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t4_wellord2])).

cnf(c_0_18,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | r2_hidden(esk2_1(k1_wellord2(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_13]),c_0_16])).

fof(c_0_20,negated_conjecture,
    ( v3_ordinal1(esk6_0)
    & ~ v6_relat_2(k1_wellord2(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_1(X1),k3_relat_1(X1))
    | v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X14,X15] :
      ( ~ v3_ordinal1(X14)
      | ~ v3_ordinal1(X15)
      | r1_ordinal1(X14,X15)
      | r2_hidden(X15,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_23,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | v3_ordinal1(esk2_1(k1_wellord2(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v3_ordinal1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( ~ v6_relat_2(k1_wellord2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | r2_hidden(esk3_1(k1_wellord2(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_13]),c_0_16])).

cnf(c_0_27,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v3_ordinal1(esk2_1(k1_wellord2(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_29,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | v3_ordinal1(esk3_1(k1_wellord2(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_26])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_31,plain,(
    ! [X10,X11] :
      ( ( ~ r1_ordinal1(X10,X11)
        | r1_tarski(X10,X11)
        | ~ v3_ordinal1(X10)
        | ~ v3_ordinal1(X11) )
      & ( ~ r1_tarski(X10,X11)
        | r1_ordinal1(X10,X11)
        | ~ v3_ordinal1(X10)
        | ~ v3_ordinal1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_32,negated_conjecture,
    ( r1_ordinal1(X1,esk2_1(k1_wellord2(esk6_0)))
    | r2_hidden(esk2_1(k1_wellord2(esk6_0)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( v3_ordinal1(esk3_1(k1_wellord2(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_24]),c_0_25])).

cnf(c_0_34,plain,
    ( v6_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk3_1(X1),esk2_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]),c_0_13])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( r1_ordinal1(esk3_1(k1_wellord2(esk6_0)),esk2_1(k1_wellord2(esk6_0)))
    | r2_hidden(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

fof(c_0_38,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_ordinal1(X6)
        | ~ r2_hidden(X7,X6)
        | r1_tarski(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_ordinal1(X8) )
      & ( ~ r1_tarski(esk1_1(X8),X8)
        | v1_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

cnf(c_0_39,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk3_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_13])]),c_0_26]),c_0_19])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk3_1(k1_wellord2(esk6_0)),esk2_1(k1_wellord2(esk6_0)))
    | r2_hidden(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_28]),c_0_33])])).

cnf(c_0_41,plain,
    ( v6_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_25])).

cnf(c_0_44,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_13])]),c_0_19]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0)))
    | ~ v1_ordinal1(esk3_1(k1_wellord2(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_46,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_ordinal1(esk3_1(k1_wellord2(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_25])).

cnf(c_0_48,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:51:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  # Presaturation interreduction done
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.38  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.12/0.38  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.12/0.38  fof(t4_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>v6_relat_2(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_wellord2)).
% 0.12/0.38  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.12/0.38  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.12/0.38  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.12/0.38  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.12/0.38  fof(c_0_9, plain, ![X21, X22, X23, X24]:(((k3_relat_1(X22)=X21|X22!=k1_wellord2(X21)|~v1_relat_1(X22))&((~r2_hidden(k4_tarski(X23,X24),X22)|r1_tarski(X23,X24)|(~r2_hidden(X23,X21)|~r2_hidden(X24,X21))|X22!=k1_wellord2(X21)|~v1_relat_1(X22))&(~r1_tarski(X23,X24)|r2_hidden(k4_tarski(X23,X24),X22)|(~r2_hidden(X23,X21)|~r2_hidden(X24,X21))|X22!=k1_wellord2(X21)|~v1_relat_1(X22))))&(((r2_hidden(esk4_2(X21,X22),X21)|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22))&(r2_hidden(esk5_2(X21,X22),X21)|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22)))&((~r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X22)|~r1_tarski(esk4_2(X21,X22),esk5_2(X21,X22))|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22))&(r2_hidden(k4_tarski(esk4_2(X21,X22),esk5_2(X21,X22)),X22)|r1_tarski(esk4_2(X21,X22),esk5_2(X21,X22))|k3_relat_1(X22)!=X21|X22=k1_wellord2(X21)|~v1_relat_1(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.38  fof(c_0_10, plain, ![X27]:v1_relat_1(k1_wellord2(X27)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.38  fof(c_0_11, plain, ![X16, X17, X18]:((~v6_relat_2(X16)|(~r2_hidden(X17,k3_relat_1(X16))|~r2_hidden(X18,k3_relat_1(X16))|X17=X18|r2_hidden(k4_tarski(X17,X18),X16)|r2_hidden(k4_tarski(X18,X17),X16))|~v1_relat_1(X16))&(((((r2_hidden(esk2_1(X16),k3_relat_1(X16))|v6_relat_2(X16)|~v1_relat_1(X16))&(r2_hidden(esk3_1(X16),k3_relat_1(X16))|v6_relat_2(X16)|~v1_relat_1(X16)))&(esk2_1(X16)!=esk3_1(X16)|v6_relat_2(X16)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk2_1(X16),esk3_1(X16)),X16)|v6_relat_2(X16)|~v1_relat_1(X16)))&(~r2_hidden(k4_tarski(esk3_1(X16),esk2_1(X16)),X16)|v6_relat_2(X16)|~v1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.12/0.38  cnf(c_0_12, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  cnf(c_0_13, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.38  fof(c_0_14, plain, ![X12, X13]:(~v3_ordinal1(X13)|(~r2_hidden(X12,X13)|v3_ordinal1(X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.12/0.38  cnf(c_0_15, plain, (r2_hidden(esk2_1(X1),k3_relat_1(X1))|v6_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_16, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])])).
% 0.12/0.38  fof(c_0_17, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v6_relat_2(k1_wellord2(X1)))), inference(assume_negation,[status(cth)],[t4_wellord2])).
% 0.12/0.38  cnf(c_0_18, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.38  cnf(c_0_19, plain, (v6_relat_2(k1_wellord2(X1))|r2_hidden(esk2_1(k1_wellord2(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_13]), c_0_16])).
% 0.12/0.38  fof(c_0_20, negated_conjecture, (v3_ordinal1(esk6_0)&~v6_relat_2(k1_wellord2(esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.12/0.38  cnf(c_0_21, plain, (r2_hidden(esk3_1(X1),k3_relat_1(X1))|v6_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  fof(c_0_22, plain, ![X14, X15]:(~v3_ordinal1(X14)|(~v3_ordinal1(X15)|(r1_ordinal1(X14,X15)|r2_hidden(X15,X14)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.12/0.38  cnf(c_0_23, plain, (v6_relat_2(k1_wellord2(X1))|v3_ordinal1(esk2_1(k1_wellord2(X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_24, negated_conjecture, (v3_ordinal1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_25, negated_conjecture, (~v6_relat_2(k1_wellord2(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_26, plain, (v6_relat_2(k1_wellord2(X1))|r2_hidden(esk3_1(k1_wellord2(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_13]), c_0_16])).
% 0.12/0.38  cnf(c_0_27, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  cnf(c_0_28, negated_conjecture, (v3_ordinal1(esk2_1(k1_wellord2(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.12/0.38  cnf(c_0_29, plain, (v6_relat_2(k1_wellord2(X1))|v3_ordinal1(esk3_1(k1_wellord2(X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_26])).
% 0.12/0.38  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.38  fof(c_0_31, plain, ![X10, X11]:((~r1_ordinal1(X10,X11)|r1_tarski(X10,X11)|(~v3_ordinal1(X10)|~v3_ordinal1(X11)))&(~r1_tarski(X10,X11)|r1_ordinal1(X10,X11)|(~v3_ordinal1(X10)|~v3_ordinal1(X11)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.12/0.38  cnf(c_0_32, negated_conjecture, (r1_ordinal1(X1,esk2_1(k1_wellord2(esk6_0)))|r2_hidden(esk2_1(k1_wellord2(esk6_0)),X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.38  cnf(c_0_33, negated_conjecture, (v3_ordinal1(esk3_1(k1_wellord2(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_24]), c_0_25])).
% 0.12/0.38  cnf(c_0_34, plain, (v6_relat_2(X1)|~r2_hidden(k4_tarski(esk3_1(X1),esk2_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r1_tarski(X1,X2)|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_30]), c_0_13])])).
% 0.12/0.38  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.38  cnf(c_0_37, negated_conjecture, (r1_ordinal1(esk3_1(k1_wellord2(esk6_0)),esk2_1(k1_wellord2(esk6_0)))|r2_hidden(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0)))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.12/0.38  fof(c_0_38, plain, ![X6, X7, X8]:((~v1_ordinal1(X6)|(~r2_hidden(X7,X6)|r1_tarski(X7,X6)))&((r2_hidden(esk1_1(X8),X8)|v1_ordinal1(X8))&(~r1_tarski(esk1_1(X8),X8)|v1_ordinal1(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.12/0.38  cnf(c_0_39, plain, (v6_relat_2(k1_wellord2(X1))|~r1_tarski(esk3_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_13])]), c_0_26]), c_0_19])).
% 0.12/0.38  cnf(c_0_40, negated_conjecture, (r1_tarski(esk3_1(k1_wellord2(esk6_0)),esk2_1(k1_wellord2(esk6_0)))|r2_hidden(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_28]), c_0_33])])).
% 0.12/0.38  cnf(c_0_41, plain, (v6_relat_2(X1)|~r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.38  cnf(c_0_42, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_25])).
% 0.12/0.38  cnf(c_0_44, plain, (v6_relat_2(k1_wellord2(X1))|~r1_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_13])]), c_0_19]), c_0_26])).
% 0.12/0.38  cnf(c_0_45, negated_conjecture, (r1_tarski(esk2_1(k1_wellord2(esk6_0)),esk3_1(k1_wellord2(esk6_0)))|~v1_ordinal1(esk3_1(k1_wellord2(esk6_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.38  fof(c_0_46, plain, ![X5]:((v1_ordinal1(X5)|~v3_ordinal1(X5))&(v2_ordinal1(X5)|~v3_ordinal1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.12/0.38  cnf(c_0_47, negated_conjecture, (~v1_ordinal1(esk3_1(k1_wellord2(esk6_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_25])).
% 0.12/0.38  cnf(c_0_48, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_33])]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 50
% 0.12/0.38  # Proof object clause steps            : 31
% 0.12/0.38  # Proof object formula steps           : 19
% 0.12/0.38  # Proof object conjectures             : 14
% 0.12/0.38  # Proof object clause conjectures      : 11
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 14
% 0.12/0.38  # Proof object initial formulas used   : 9
% 0.12/0.38  # Proof object generating inferences   : 15
% 0.12/0.38  # Proof object simplifying inferences  : 25
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 9
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 25
% 0.12/0.38  # Removed in clause preprocessing      : 0
% 0.12/0.38  # Initial clauses in saturation        : 25
% 0.12/0.38  # Processed clauses                    : 140
% 0.12/0.38  # ...of these trivial                  : 0
% 0.12/0.38  # ...subsumed                          : 1
% 0.12/0.38  # ...remaining for further processing  : 139
% 0.12/0.38  # Other redundant clauses eliminated   : 7
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 2
% 0.12/0.38  # Backward-rewritten                   : 4
% 0.12/0.38  # Generated clauses                    : 241
% 0.12/0.38  # ...of the previous two non-trivial   : 231
% 0.12/0.38  # Contextual simplify-reflections      : 12
% 0.12/0.38  # Paramodulations                      : 234
% 0.12/0.38  # Factorizations                       : 0
% 0.12/0.38  # Equation resolutions                 : 7
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 101
% 0.12/0.38  #    Positive orientable unit clauses  : 9
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 2
% 0.12/0.38  #    Non-unit-clauses                  : 90
% 0.12/0.38  # Current number of unprocessed clauses: 141
% 0.12/0.38  # ...number of literals in the above   : 570
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 31
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 2861
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 1503
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 13
% 0.12/0.38  # Unit Clause-clause subsumption calls : 125
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 8
% 0.12/0.38  # BW rewrite match successes           : 4
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 8135
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.034 s
% 0.12/0.38  # System time              : 0.008 s
% 0.12/0.38  # Total time               : 0.042 s
% 0.12/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
