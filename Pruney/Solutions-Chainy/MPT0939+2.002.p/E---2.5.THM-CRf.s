%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:41 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 269 expanded)
%              Number of clauses        :   28 ( 113 expanded)
%              Number of leaves         :    7 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 (1251 expanded)
%              Number of equality atoms :   21 ( 236 expanded)
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

fof(connectedness_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
        | r1_ordinal1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(c_0_7,plain,(
    ! [X16,X17,X18,X19] :
      ( ( k3_relat_1(X17) = X16
        | X17 != k1_wellord2(X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(X18,X19),X17)
        | r1_tarski(X18,X19)
        | ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X19,X16)
        | X17 != k1_wellord2(X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r1_tarski(X18,X19)
        | r2_hidden(k4_tarski(X18,X19),X17)
        | ~ r2_hidden(X18,X16)
        | ~ r2_hidden(X19,X16)
        | X17 != k1_wellord2(X16)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk3_2(X16,X17),X16)
        | k3_relat_1(X17) != X16
        | X17 = k1_wellord2(X16)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(esk4_2(X16,X17),X16)
        | k3_relat_1(X17) != X16
        | X17 = k1_wellord2(X16)
        | ~ v1_relat_1(X17) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X16,X17),esk4_2(X16,X17)),X17)
        | ~ r1_tarski(esk3_2(X16,X17),esk4_2(X16,X17))
        | k3_relat_1(X17) != X16
        | X17 = k1_wellord2(X16)
        | ~ v1_relat_1(X17) )
      & ( r2_hidden(k4_tarski(esk3_2(X16,X17),esk4_2(X16,X17)),X17)
        | r1_tarski(esk3_2(X16,X17),esk4_2(X16,X17))
        | k3_relat_1(X17) != X16
        | X17 = k1_wellord2(X16)
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_8,plain,(
    ! [X22] : v1_relat_1(k1_wellord2(X22)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_9,plain,(
    ! [X11,X12,X13] :
      ( ( ~ v6_relat_2(X11)
        | ~ r2_hidden(X12,k3_relat_1(X11))
        | ~ r2_hidden(X13,k3_relat_1(X11))
        | X12 = X13
        | r2_hidden(k4_tarski(X12,X13),X11)
        | r2_hidden(k4_tarski(X13,X12),X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk1_1(X11),k3_relat_1(X11))
        | v6_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_1(X11),k3_relat_1(X11))
        | v6_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( esk1_1(X11) != esk2_1(X11)
        | v6_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk1_1(X11),esk2_1(X11)),X11)
        | v6_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk2_1(X11),esk1_1(X11)),X11)
        | v6_relat_2(X11)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).

cnf(c_0_10,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X9,X10] :
      ( ~ v3_ordinal1(X10)
      | ~ r2_hidden(X9,X10)
      | v3_ordinal1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_1(X1),k3_relat_1(X1))
    | v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => v6_relat_2(k1_wellord2(X1)) ) ),
    inference(assume_negation,[status(cth)],[t4_wellord2])).

cnf(c_0_16,plain,
    ( v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | r2_hidden(esk1_1(k1_wellord2(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_11]),c_0_14])).

fof(c_0_18,negated_conjecture,
    ( v3_ordinal1(esk5_0)
    & ~ v6_relat_2(k1_wellord2(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_1(X1),k3_relat_1(X1))
    | v6_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(X6)
      | r1_ordinal1(X5,X6)
      | r1_ordinal1(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).

cnf(c_0_21,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | v3_ordinal1(esk1_1(k1_wellord2(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v3_ordinal1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ v6_relat_2(k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | r2_hidden(esk2_1(k1_wellord2(X1)),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_14])).

cnf(c_0_25,plain,
    ( r1_ordinal1(X1,X2)
    | r1_ordinal1(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v3_ordinal1(esk1_1(k1_wellord2(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])).

cnf(c_0_27,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | v3_ordinal1(esk2_1(k1_wellord2(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_24])).

fof(c_0_28,plain,(
    ! [X7,X8] :
      ( ( ~ r1_ordinal1(X7,X8)
        | r1_tarski(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) )
      & ( ~ r1_tarski(X7,X8)
        | r1_ordinal1(X7,X8)
        | ~ v3_ordinal1(X7)
        | ~ v3_ordinal1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_29,negated_conjecture,
    ( r1_ordinal1(X1,esk1_1(k1_wellord2(esk5_0)))
    | r1_ordinal1(esk1_1(k1_wellord2(esk5_0)),X1)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(esk2_1(k1_wellord2(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_22]),c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_ordinal1(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0)))
    | r1_ordinal1(esk2_1(k1_wellord2(esk5_0)),esk1_1(k1_wellord2(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,plain,
    ( v6_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk2_1(X1),esk1_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_11])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_1(k1_wellord2(esk5_0)),esk1_1(k1_wellord2(esk5_0)))
    | r1_ordinal1(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_26]),c_0_30])])).

cnf(c_0_37,plain,
    ( v6_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk1_1(X1),esk2_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_11])]),c_0_24]),c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(esk2_1(k1_wellord2(esk5_0)),esk1_1(k1_wellord2(esk5_0)))
    | r1_tarski(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_36]),c_0_30]),c_0_26])])).

cnf(c_0_40,plain,
    ( v6_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_35]),c_0_11])]),c_0_17]),c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_23])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:58:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.028 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.18/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.18/0.37  fof(l4_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v6_relat_2(X1)<=>![X2, X3]:~(((((r2_hidden(X2,k3_relat_1(X1))&r2_hidden(X3,k3_relat_1(X1)))&X2!=X3)&~(r2_hidden(k4_tarski(X2,X3),X1)))&~(r2_hidden(k4_tarski(X3,X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l4_wellord1)).
% 0.18/0.37  fof(t23_ordinal1, axiom, ![X1, X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)=>v3_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 0.18/0.37  fof(t4_wellord2, conjecture, ![X1]:(v3_ordinal1(X1)=>v6_relat_2(k1_wellord2(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_wellord2)).
% 0.18/0.37  fof(connectedness_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 0.18/0.37  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.18/0.37  fof(c_0_7, plain, ![X16, X17, X18, X19]:(((k3_relat_1(X17)=X16|X17!=k1_wellord2(X16)|~v1_relat_1(X17))&((~r2_hidden(k4_tarski(X18,X19),X17)|r1_tarski(X18,X19)|(~r2_hidden(X18,X16)|~r2_hidden(X19,X16))|X17!=k1_wellord2(X16)|~v1_relat_1(X17))&(~r1_tarski(X18,X19)|r2_hidden(k4_tarski(X18,X19),X17)|(~r2_hidden(X18,X16)|~r2_hidden(X19,X16))|X17!=k1_wellord2(X16)|~v1_relat_1(X17))))&(((r2_hidden(esk3_2(X16,X17),X16)|k3_relat_1(X17)!=X16|X17=k1_wellord2(X16)|~v1_relat_1(X17))&(r2_hidden(esk4_2(X16,X17),X16)|k3_relat_1(X17)!=X16|X17=k1_wellord2(X16)|~v1_relat_1(X17)))&((~r2_hidden(k4_tarski(esk3_2(X16,X17),esk4_2(X16,X17)),X17)|~r1_tarski(esk3_2(X16,X17),esk4_2(X16,X17))|k3_relat_1(X17)!=X16|X17=k1_wellord2(X16)|~v1_relat_1(X17))&(r2_hidden(k4_tarski(esk3_2(X16,X17),esk4_2(X16,X17)),X17)|r1_tarski(esk3_2(X16,X17),esk4_2(X16,X17))|k3_relat_1(X17)!=X16|X17=k1_wellord2(X16)|~v1_relat_1(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.18/0.37  fof(c_0_8, plain, ![X22]:v1_relat_1(k1_wellord2(X22)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.18/0.37  fof(c_0_9, plain, ![X11, X12, X13]:((~v6_relat_2(X11)|(~r2_hidden(X12,k3_relat_1(X11))|~r2_hidden(X13,k3_relat_1(X11))|X12=X13|r2_hidden(k4_tarski(X12,X13),X11)|r2_hidden(k4_tarski(X13,X12),X11))|~v1_relat_1(X11))&(((((r2_hidden(esk1_1(X11),k3_relat_1(X11))|v6_relat_2(X11)|~v1_relat_1(X11))&(r2_hidden(esk2_1(X11),k3_relat_1(X11))|v6_relat_2(X11)|~v1_relat_1(X11)))&(esk1_1(X11)!=esk2_1(X11)|v6_relat_2(X11)|~v1_relat_1(X11)))&(~r2_hidden(k4_tarski(esk1_1(X11),esk2_1(X11)),X11)|v6_relat_2(X11)|~v1_relat_1(X11)))&(~r2_hidden(k4_tarski(esk2_1(X11),esk1_1(X11)),X11)|v6_relat_2(X11)|~v1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l4_wellord1])])])])])])).
% 0.18/0.37  cnf(c_0_10, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.37  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.37  fof(c_0_12, plain, ![X9, X10]:(~v3_ordinal1(X10)|(~r2_hidden(X9,X10)|v3_ordinal1(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t23_ordinal1])])).
% 0.18/0.37  cnf(c_0_13, plain, (r2_hidden(esk1_1(X1),k3_relat_1(X1))|v6_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_14, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])])).
% 0.18/0.37  fof(c_0_15, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>v6_relat_2(k1_wellord2(X1)))), inference(assume_negation,[status(cth)],[t4_wellord2])).
% 0.18/0.37  cnf(c_0_16, plain, (v3_ordinal1(X2)|~v3_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.18/0.37  cnf(c_0_17, plain, (v6_relat_2(k1_wellord2(X1))|r2_hidden(esk1_1(k1_wellord2(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_11]), c_0_14])).
% 0.18/0.37  fof(c_0_18, negated_conjecture, (v3_ordinal1(esk5_0)&~v6_relat_2(k1_wellord2(esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.18/0.37  cnf(c_0_19, plain, (r2_hidden(esk2_1(X1),k3_relat_1(X1))|v6_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  fof(c_0_20, plain, ![X5, X6]:(~v3_ordinal1(X5)|~v3_ordinal1(X6)|(r1_ordinal1(X5,X6)|r1_ordinal1(X6,X5))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[connectedness_r1_ordinal1])])).
% 0.18/0.37  cnf(c_0_21, plain, (v6_relat_2(k1_wellord2(X1))|v3_ordinal1(esk1_1(k1_wellord2(X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (v3_ordinal1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (~v6_relat_2(k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.37  cnf(c_0_24, plain, (v6_relat_2(k1_wellord2(X1))|r2_hidden(esk2_1(k1_wellord2(X1)),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_11]), c_0_14])).
% 0.18/0.37  cnf(c_0_25, plain, (r1_ordinal1(X1,X2)|r1_ordinal1(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (v3_ordinal1(esk1_1(k1_wellord2(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])).
% 0.18/0.37  cnf(c_0_27, plain, (v6_relat_2(k1_wellord2(X1))|v3_ordinal1(esk2_1(k1_wellord2(X1)))|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_16, c_0_24])).
% 0.18/0.37  fof(c_0_28, plain, ![X7, X8]:((~r1_ordinal1(X7,X8)|r1_tarski(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))&(~r1_tarski(X7,X8)|r1_ordinal1(X7,X8)|(~v3_ordinal1(X7)|~v3_ordinal1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.18/0.37  cnf(c_0_29, negated_conjecture, (r1_ordinal1(X1,esk1_1(k1_wellord2(esk5_0)))|r1_ordinal1(esk1_1(k1_wellord2(esk5_0)),X1)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.37  cnf(c_0_30, negated_conjecture, (v3_ordinal1(esk2_1(k1_wellord2(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_22]), c_0_23])).
% 0.18/0.37  cnf(c_0_31, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.37  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.18/0.37  cnf(c_0_33, negated_conjecture, (r1_ordinal1(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0)))|r1_ordinal1(esk2_1(k1_wellord2(esk5_0)),esk1_1(k1_wellord2(esk5_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.18/0.37  cnf(c_0_34, plain, (v6_relat_2(X1)|~r2_hidden(k4_tarski(esk2_1(X1),esk1_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_35, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_11])])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (r1_tarski(esk2_1(k1_wellord2(esk5_0)),esk1_1(k1_wellord2(esk5_0)))|r1_ordinal1(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_26]), c_0_30])])).
% 0.18/0.37  cnf(c_0_37, plain, (v6_relat_2(X1)|~r2_hidden(k4_tarski(esk1_1(X1),esk2_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.37  cnf(c_0_38, plain, (v6_relat_2(k1_wellord2(X1))|~r1_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_11])]), c_0_24]), c_0_17])).
% 0.18/0.37  cnf(c_0_39, negated_conjecture, (r1_tarski(esk2_1(k1_wellord2(esk5_0)),esk1_1(k1_wellord2(esk5_0)))|r1_tarski(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_36]), c_0_30]), c_0_26])])).
% 0.18/0.37  cnf(c_0_40, plain, (v6_relat_2(k1_wellord2(X1))|~r1_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_35]), c_0_11])]), c_0_17]), c_0_24])).
% 0.18/0.37  cnf(c_0_41, negated_conjecture, (r1_tarski(esk1_1(k1_wellord2(esk5_0)),esk2_1(k1_wellord2(esk5_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_23])).
% 0.18/0.37  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_23]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 43
% 0.18/0.37  # Proof object clause steps            : 28
% 0.18/0.37  # Proof object formula steps           : 15
% 0.18/0.37  # Proof object conjectures             : 13
% 0.18/0.37  # Proof object clause conjectures      : 10
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 12
% 0.18/0.37  # Proof object initial formulas used   : 7
% 0.18/0.37  # Proof object generating inferences   : 14
% 0.18/0.37  # Proof object simplifying inferences  : 26
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 7
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 20
% 0.18/0.37  # Removed in clause preprocessing      : 0
% 0.18/0.37  # Initial clauses in saturation        : 20
% 0.18/0.37  # Processed clauses                    : 125
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 7
% 0.18/0.37  # ...remaining for further processing  : 118
% 0.18/0.37  # Other redundant clauses eliminated   : 7
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 1
% 0.18/0.37  # Generated clauses                    : 204
% 0.18/0.37  # ...of the previous two non-trivial   : 195
% 0.18/0.37  # Contextual simplify-reflections      : 16
% 0.18/0.37  # Paramodulations                      : 197
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 7
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 90
% 0.18/0.37  #    Positive orientable unit clauses  : 12
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 1
% 0.18/0.37  #    Non-unit-clauses                  : 77
% 0.18/0.37  # Current number of unprocessed clauses: 110
% 0.18/0.37  # ...number of literals in the above   : 452
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 21
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 2419
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 991
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 23
% 0.18/0.37  # Unit Clause-clause subsumption calls : 129
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 3
% 0.18/0.37  # BW rewrite match successes           : 1
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 7224
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.037 s
% 0.18/0.37  # System time              : 0.003 s
% 0.18/0.37  # Total time               : 0.041 s
% 0.18/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
