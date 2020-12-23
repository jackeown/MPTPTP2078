%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:49:24 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 214 expanded)
%              Number of clauses        :   27 ( 107 expanded)
%              Number of leaves         :    5 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 (1104 expanded)
%              Number of equality atoms :   56 ( 393 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( X2 = k6_relat_1(X1)
      <=> ! [X3,X4] :
            ( r2_hidden(k4_tarski(X3,X4),X2)
          <=> ( r2_hidden(X3,X1)
              & X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t71_relat_1,conjecture,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_5,plain,(
    ! [X5,X6,X7,X8,X9,X10] :
      ( ( r2_hidden(X7,X5)
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( X7 = X8
        | ~ r2_hidden(k4_tarski(X7,X8),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(X9,X5)
        | X9 != X10
        | r2_hidden(k4_tarski(X9,X10),X6)
        | X6 != k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | ~ r2_hidden(esk1_2(X5,X6),X5)
        | esk1_2(X5,X6) != esk2_2(X5,X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) )
      & ( esk1_2(X5,X6) = esk2_2(X5,X6)
        | r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)
        | X6 = k6_relat_1(X5)
        | ~ v1_relat_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).

fof(c_0_6,plain,(
    ! [X35] : v1_relat_1(k6_relat_1(X35)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

fof(c_0_7,plain,(
    ! [X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( ~ r2_hidden(X26,X25)
        | r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X26),X24)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(X29,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k2_relat_1(X24) )
      & ( ~ r2_hidden(esk7_2(X30,X31),X31)
        | ~ r2_hidden(k4_tarski(X33,esk7_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) )
      & ( r2_hidden(esk7_2(X30,X31),X31)
        | r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)
        | X31 = k2_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(k4_tarski(X1,X3),X4)
    | ~ r2_hidden(X1,X2)
    | X1 != X3
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X3 != k6_relat_1(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),X4)
    | X4 != k6_relat_1(X2)
    | ~ v1_relat_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_12,plain,(
    ! [X13,X14,X15,X17,X18,X19,X20,X22] :
      ( ( ~ r2_hidden(X15,X14)
        | r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X13)
        | r2_hidden(X17,X14)
        | X14 != k1_relat_1(X13) )
      & ( ~ r2_hidden(esk4_2(X19,X20),X20)
        | ~ r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)
        | X20 = k1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X19,X20),X20)
        | r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)
        | X20 = k1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_13,plain,
    ( X2 = k2_relat_1(X1)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(X3,esk7_2(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])]),c_0_9])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_9])])).

cnf(c_0_16,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_9])])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( X1 = k2_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(esk7_2(k6_relat_1(X2),X1),X1)
    | ~ r2_hidden(esk7_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( esk8_2(k6_relat_1(X1),X2) = esk7_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | r2_hidden(esk7_2(k6_relat_1(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( X2 = k1_relat_1(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(k4_tarski(esk4_2(X1,X2),X3),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( X1 = k1_relat_1(k6_relat_1(X2))
    | r2_hidden(esk4_2(k6_relat_1(X2),X1),X1)
    | r2_hidden(esk4_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( k1_relat_1(k6_relat_1(X1)) = X1
        & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    inference(assume_negation,[status(cth)],[t71_relat_1])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( esk8_2(k6_relat_1(X1),X2) = esk7_2(k6_relat_1(X1),X2)
    | X2 = k2_relat_1(k6_relat_1(X1))
    | ~ r2_hidden(esk7_2(k6_relat_1(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,plain,
    ( X1 = k1_relat_1(k6_relat_1(X2))
    | ~ r2_hidden(esk4_2(k6_relat_1(X2),X1),X1)
    | ~ r2_hidden(esk4_2(k6_relat_1(X2),X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_28,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1
    | r2_hidden(esk4_2(k6_relat_1(X1),X1),X1) ),
    inference(ef,[status(thm)],[c_0_23])).

fof(c_0_29,negated_conjecture,
    ( k1_relat_1(k6_relat_1(esk9_0)) != esk9_0
    | k2_relat_1(k6_relat_1(esk9_0)) != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

cnf(c_0_30,plain,
    ( X1 = k2_relat_1(X2)
    | r2_hidden(esk8_2(X2,X1),k1_relat_1(X2))
    | r2_hidden(esk7_2(X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_16])).

cnf(c_0_31,plain,
    ( esk8_2(k6_relat_1(X1),X1) = esk7_2(k6_relat_1(X1),X1)
    | k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_32,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k1_relat_1(k6_relat_1(esk9_0)) != esk9_0
    | k2_relat_1(k6_relat_1(esk9_0)) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_34,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1
    | r2_hidden(esk7_2(k6_relat_1(X1),X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_35,negated_conjecture,
    ( k2_relat_1(k6_relat_1(esk9_0)) != esk9_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_32])])).

cnf(c_0_36,plain,
    ( k2_relat_1(k6_relat_1(X1)) = X1 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_34]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.49  # AutoSched0-Mode selected heuristic G_E___208_C02CMA_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.49  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.49  #
% 0.20/0.49  # Preprocessing time       : 0.028 s
% 0.20/0.49  # Presaturation interreduction done
% 0.20/0.49  
% 0.20/0.49  # Proof found!
% 0.20/0.49  # SZS status Theorem
% 0.20/0.49  # SZS output start CNFRefutation
% 0.20/0.49  fof(d10_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k6_relat_1(X1)<=>![X3, X4]:(r2_hidden(k4_tarski(X3,X4),X2)<=>(r2_hidden(X3,X1)&X3=X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 0.20/0.49  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.20/0.49  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.49  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.49  fof(t71_relat_1, conjecture, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.20/0.49  fof(c_0_5, plain, ![X5, X6, X7, X8, X9, X10]:((((r2_hidden(X7,X5)|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6))&(X7=X8|~r2_hidden(k4_tarski(X7,X8),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&(~r2_hidden(X9,X5)|X9!=X10|r2_hidden(k4_tarski(X9,X10),X6)|X6!=k6_relat_1(X5)|~v1_relat_1(X6)))&((~r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|(~r2_hidden(esk1_2(X5,X6),X5)|esk1_2(X5,X6)!=esk2_2(X5,X6))|X6=k6_relat_1(X5)|~v1_relat_1(X6))&((r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))&(esk1_2(X5,X6)=esk2_2(X5,X6)|r2_hidden(k4_tarski(esk1_2(X5,X6),esk2_2(X5,X6)),X6)|X6=k6_relat_1(X5)|~v1_relat_1(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_relat_1])])])])])])).
% 0.20/0.49  fof(c_0_6, plain, ![X35]:v1_relat_1(k6_relat_1(X35)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.20/0.49  fof(c_0_7, plain, ![X24, X25, X26, X28, X29, X30, X31, X33]:(((~r2_hidden(X26,X25)|r2_hidden(k4_tarski(esk6_3(X24,X25,X26),X26),X24)|X25!=k2_relat_1(X24))&(~r2_hidden(k4_tarski(X29,X28),X24)|r2_hidden(X28,X25)|X25!=k2_relat_1(X24)))&((~r2_hidden(esk7_2(X30,X31),X31)|~r2_hidden(k4_tarski(X33,esk7_2(X30,X31)),X30)|X31=k2_relat_1(X30))&(r2_hidden(esk7_2(X30,X31),X31)|r2_hidden(k4_tarski(esk8_2(X30,X31),esk7_2(X30,X31)),X30)|X31=k2_relat_1(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.49  cnf(c_0_8, plain, (r2_hidden(k4_tarski(X1,X3),X4)|~r2_hidden(X1,X2)|X1!=X3|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.49  cnf(c_0_9, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.49  cnf(c_0_10, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),X3)|X3!=k6_relat_1(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.49  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),X4)|X4!=k6_relat_1(X2)|~v1_relat_1(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.49  fof(c_0_12, plain, ![X13, X14, X15, X17, X18, X19, X20, X22]:(((~r2_hidden(X15,X14)|r2_hidden(k4_tarski(X15,esk3_3(X13,X14,X15)),X13)|X14!=k1_relat_1(X13))&(~r2_hidden(k4_tarski(X17,X18),X13)|r2_hidden(X17,X14)|X14!=k1_relat_1(X13)))&((~r2_hidden(esk4_2(X19,X20),X20)|~r2_hidden(k4_tarski(esk4_2(X19,X20),X22),X19)|X20=k1_relat_1(X19))&(r2_hidden(esk4_2(X19,X20),X20)|r2_hidden(k4_tarski(esk4_2(X19,X20),esk5_2(X19,X20)),X19)|X20=k1_relat_1(X19)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.49  cnf(c_0_13, plain, (X2=k2_relat_1(X1)|~r2_hidden(esk7_2(X1,X2),X2)|~r2_hidden(k4_tarski(X3,esk7_2(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.49  cnf(c_0_14, plain, (r2_hidden(k4_tarski(X1,X1),k6_relat_1(X2))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_8])]), c_0_9])])).
% 0.20/0.49  cnf(c_0_15, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X2),k6_relat_1(X3))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_9])])).
% 0.20/0.49  cnf(c_0_16, plain, (r2_hidden(esk7_2(X1,X2),X2)|r2_hidden(k4_tarski(esk8_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.49  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k6_relat_1(X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_9])])).
% 0.20/0.49  cnf(c_0_18, plain, (r2_hidden(esk4_2(X1,X2),X2)|r2_hidden(k4_tarski(esk4_2(X1,X2),esk5_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.49  cnf(c_0_19, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.49  cnf(c_0_20, plain, (X1=k2_relat_1(k6_relat_1(X2))|~r2_hidden(esk7_2(k6_relat_1(X2),X1),X1)|~r2_hidden(esk7_2(k6_relat_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.20/0.49  cnf(c_0_21, plain, (esk8_2(k6_relat_1(X1),X2)=esk7_2(k6_relat_1(X1),X2)|X2=k2_relat_1(k6_relat_1(X1))|r2_hidden(esk7_2(k6_relat_1(X1),X2),X2)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.49  cnf(c_0_22, plain, (X2=k1_relat_1(X1)|~r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(k4_tarski(esk4_2(X1,X2),X3),X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.49  cnf(c_0_23, plain, (X1=k1_relat_1(k6_relat_1(X2))|r2_hidden(esk4_2(k6_relat_1(X2),X1),X1)|r2_hidden(esk4_2(k6_relat_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.49  fof(c_0_24, negated_conjecture, ~(![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1)), inference(assume_negation,[status(cth)],[t71_relat_1])).
% 0.20/0.49  cnf(c_0_25, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.49  cnf(c_0_26, plain, (esk8_2(k6_relat_1(X1),X2)=esk7_2(k6_relat_1(X1),X2)|X2=k2_relat_1(k6_relat_1(X1))|~r2_hidden(esk7_2(k6_relat_1(X1),X2),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.49  cnf(c_0_27, plain, (X1=k1_relat_1(k6_relat_1(X2))|~r2_hidden(esk4_2(k6_relat_1(X2),X1),X1)|~r2_hidden(esk4_2(k6_relat_1(X2),X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.20/0.49  cnf(c_0_28, plain, (k1_relat_1(k6_relat_1(X1))=X1|r2_hidden(esk4_2(k6_relat_1(X1),X1),X1)), inference(ef,[status(thm)],[c_0_23])).
% 0.20/0.49  fof(c_0_29, negated_conjecture, (k1_relat_1(k6_relat_1(esk9_0))!=esk9_0|k2_relat_1(k6_relat_1(esk9_0))!=esk9_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.20/0.49  cnf(c_0_30, plain, (X1=k2_relat_1(X2)|r2_hidden(esk8_2(X2,X1),k1_relat_1(X2))|r2_hidden(esk7_2(X2,X1),X1)), inference(spm,[status(thm)],[c_0_25, c_0_16])).
% 0.20/0.49  cnf(c_0_31, plain, (esk8_2(k6_relat_1(X1),X1)=esk7_2(k6_relat_1(X1),X1)|k2_relat_1(k6_relat_1(X1))=X1), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.20/0.49  cnf(c_0_32, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_28])).
% 0.20/0.49  cnf(c_0_33, negated_conjecture, (k1_relat_1(k6_relat_1(esk9_0))!=esk9_0|k2_relat_1(k6_relat_1(esk9_0))!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.49  cnf(c_0_34, plain, (k2_relat_1(k6_relat_1(X1))=X1|r2_hidden(esk7_2(k6_relat_1(X1),X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.20/0.49  cnf(c_0_35, negated_conjecture, (k2_relat_1(k6_relat_1(esk9_0))!=esk9_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_32])])).
% 0.20/0.49  cnf(c_0_36, plain, (k2_relat_1(k6_relat_1(X1))=X1), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_34]), c_0_34])).
% 0.20/0.49  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.20/0.49  # SZS output end CNFRefutation
% 0.20/0.49  # Proof object total steps             : 38
% 0.20/0.49  # Proof object clause steps            : 27
% 0.20/0.49  # Proof object formula steps           : 11
% 0.20/0.49  # Proof object conjectures             : 6
% 0.20/0.49  # Proof object clause conjectures      : 3
% 0.20/0.49  # Proof object formula conjectures     : 3
% 0.20/0.49  # Proof object initial clauses used    : 10
% 0.20/0.49  # Proof object initial formulas used   : 5
% 0.20/0.49  # Proof object generating inferences   : 11
% 0.20/0.49  # Proof object simplifying inferences  : 19
% 0.20/0.49  # Training examples: 0 positive, 0 negative
% 0.20/0.49  # Parsed axioms                        : 5
% 0.20/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.49  # Initial clauses                      : 16
% 0.20/0.49  # Removed in clause preprocessing      : 0
% 0.20/0.49  # Initial clauses in saturation        : 16
% 0.20/0.49  # Processed clauses                    : 393
% 0.20/0.49  # ...of these trivial                  : 0
% 0.20/0.49  # ...subsumed                          : 100
% 0.20/0.49  # ...remaining for further processing  : 293
% 0.20/0.49  # Other redundant clauses eliminated   : 8
% 0.20/0.49  # Clauses deleted for lack of memory   : 0
% 0.20/0.49  # Backward-subsumed                    : 0
% 0.20/0.49  # Backward-rewritten                   : 237
% 0.20/0.49  # Generated clauses                    : 7495
% 0.20/0.49  # ...of the previous two non-trivial   : 7581
% 0.20/0.49  # Contextual simplify-reflections      : 3
% 0.20/0.49  # Paramodulations                      : 7476
% 0.20/0.49  # Factorizations                       : 12
% 0.20/0.49  # Equation resolutions                 : 8
% 0.20/0.49  # Propositional unsat checks           : 0
% 0.20/0.49  #    Propositional check models        : 0
% 0.20/0.49  #    Propositional check unsatisfiable : 0
% 0.20/0.49  #    Propositional clauses             : 0
% 0.20/0.49  #    Propositional clauses after purity: 0
% 0.20/0.49  #    Propositional unsat core size     : 0
% 0.20/0.49  #    Propositional preprocessing time  : 0.000
% 0.20/0.49  #    Propositional encoding time       : 0.000
% 0.20/0.49  #    Propositional solver time         : 0.000
% 0.20/0.49  #    Success case prop preproc time    : 0.000
% 0.20/0.49  #    Success case prop encoding time   : 0.000
% 0.20/0.49  #    Success case prop solver time     : 0.000
% 0.20/0.49  # Current number of processed clauses  : 33
% 0.20/0.49  #    Positive orientable unit clauses  : 3
% 0.20/0.49  #    Positive unorientable unit clauses: 0
% 0.20/0.49  #    Negative unit clauses             : 0
% 0.20/0.49  #    Non-unit-clauses                  : 30
% 0.20/0.49  # Current number of unprocessed clauses: 6989
% 0.20/0.49  # ...number of literals in the above   : 16711
% 0.20/0.49  # Current number of archived formulas  : 0
% 0.20/0.49  # Current number of archived clauses   : 253
% 0.20/0.49  # Clause-clause subsumption calls (NU) : 21479
% 0.20/0.49  # Rec. Clause-clause subsumption calls : 19461
% 0.20/0.49  # Non-unit clause-clause subsumptions  : 103
% 0.20/0.49  # Unit Clause-clause subsumption calls : 50
% 0.20/0.49  # Rewrite failures with RHS unbound    : 0
% 0.20/0.49  # BW rewrite match attempts            : 25
% 0.20/0.49  # BW rewrite match successes           : 25
% 0.20/0.49  # Condensation attempts                : 0
% 0.20/0.49  # Condensation successes               : 0
% 0.20/0.49  # Termbank termtop insertions          : 185224
% 0.20/0.49  
% 0.20/0.49  # -------------------------------------------------
% 0.20/0.49  # User time                : 0.141 s
% 0.20/0.49  # System time              : 0.012 s
% 0.20/0.49  # Total time               : 0.153 s
% 0.20/0.49  # Maximum resident set size: 1564 pages
%------------------------------------------------------------------------------
