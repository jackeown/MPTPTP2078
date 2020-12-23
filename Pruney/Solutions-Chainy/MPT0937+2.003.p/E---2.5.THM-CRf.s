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
% DateTime   : Thu Dec  3 11:00:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   31 (  49 expanded)
%              Number of clauses        :   18 (  22 expanded)
%              Number of leaves         :    6 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  117 ( 193 expanded)
%              Number of equality atoms :   18 (  32 expanded)
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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(d9_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
      <=> r1_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_relat_2)).

fof(t2_wellord2,conjecture,(
    ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord2)).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20] :
      ( ( k3_relat_1(X18) = X17
        | X18 != k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(X19,X20),X18)
        | r1_tarski(X19,X20)
        | ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X20,X17)
        | X18 != k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r1_tarski(X19,X20)
        | r2_hidden(k4_tarski(X19,X20),X18)
        | ~ r2_hidden(X19,X17)
        | ~ r2_hidden(X20,X17)
        | X18 != k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk3_2(X17,X18),X17)
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18)),X18)
        | ~ r1_tarski(esk3_2(X17,X18),esk4_2(X17,X18))
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) )
      & ( r2_hidden(k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18)),X18)
        | r1_tarski(esk3_2(X17,X18),esk4_2(X17,X18))
        | k3_relat_1(X18) != X17
        | X18 = k1_wellord2(X17)
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_7,plain,(
    ! [X23] : v1_relat_1(k1_wellord2(X23)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_9,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r1_relat_2(X11,X12)
        | ~ r2_hidden(X13,X12)
        | r2_hidden(k4_tarski(X13,X13),X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(esk2_2(X11,X14),X14)
        | r1_relat_2(X11,X14)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X11,X14),esk2_2(X11,X14)),X11)
        | r1_relat_2(X11,X14)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( v1_relat_1(k1_wellord2(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X16] :
      ( ( ~ v1_relat_2(X16)
        | r1_relat_2(X16,k3_relat_1(X16))
        | ~ v1_relat_1(X16) )
      & ( ~ r1_relat_2(X16,k3_relat_1(X16))
        | v1_relat_2(X16)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).

cnf(c_0_15,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk2_2(X1,X2),esk2_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]),c_0_11])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] : v1_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t2_wellord2])).

cnf(c_0_21,plain,
    ( v1_relat_2(X1)
    | ~ r1_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_15]),c_0_11])])).

cnf(c_0_23,plain,
    ( r1_relat_2(k1_wellord2(X1),X2)
    | ~ r2_hidden(esk2_2(k1_wellord2(X1),X2),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_11]),c_0_18])])).

cnf(c_0_24,plain,
    ( r1_relat_2(k1_wellord2(X1),X2)
    | r2_hidden(esk2_2(k1_wellord2(X1),X2),X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

fof(c_0_25,negated_conjecture,(
    ~ v1_relat_2(k1_wellord2(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_26,plain,
    ( v1_relat_2(k1_wellord2(X1))
    | ~ r1_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_11])])).

cnf(c_0_27,plain,
    ( r1_relat_2(k1_wellord2(X1),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_relat_2(k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,plain,
    ( v1_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:49 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.37  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 0.12/0.37  fof(d9_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v1_relat_2(X1)<=>r1_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_relat_2)).
% 0.12/0.37  fof(t2_wellord2, conjecture, ![X1]:v1_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord2)).
% 0.12/0.37  fof(c_0_6, plain, ![X17, X18, X19, X20]:(((k3_relat_1(X18)=X17|X18!=k1_wellord2(X17)|~v1_relat_1(X18))&((~r2_hidden(k4_tarski(X19,X20),X18)|r1_tarski(X19,X20)|(~r2_hidden(X19,X17)|~r2_hidden(X20,X17))|X18!=k1_wellord2(X17)|~v1_relat_1(X18))&(~r1_tarski(X19,X20)|r2_hidden(k4_tarski(X19,X20),X18)|(~r2_hidden(X19,X17)|~r2_hidden(X20,X17))|X18!=k1_wellord2(X17)|~v1_relat_1(X18))))&(((r2_hidden(esk3_2(X17,X18),X17)|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18))&(r2_hidden(esk4_2(X17,X18),X17)|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18)))&((~r2_hidden(k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18)),X18)|~r1_tarski(esk3_2(X17,X18),esk4_2(X17,X18))|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18))&(r2_hidden(k4_tarski(esk3_2(X17,X18),esk4_2(X17,X18)),X18)|r1_tarski(esk3_2(X17,X18),esk4_2(X17,X18))|k3_relat_1(X18)!=X17|X18=k1_wellord2(X17)|~v1_relat_1(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.37  fof(c_0_7, plain, ![X23]:v1_relat_1(k1_wellord2(X23)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.37  fof(c_0_8, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X11, X12, X13, X14]:((~r1_relat_2(X11,X12)|(~r2_hidden(X13,X12)|r2_hidden(k4_tarski(X13,X13),X11))|~v1_relat_1(X11))&((r2_hidden(esk2_2(X11,X14),X14)|r1_relat_2(X11,X14)|~v1_relat_1(X11))&(~r2_hidden(k4_tarski(esk2_2(X11,X14),esk2_2(X11,X14)),X11)|r1_relat_2(X11,X14)|~v1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 0.12/0.37  cnf(c_0_10, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_12, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_14, plain, ![X16]:((~v1_relat_2(X16)|r1_relat_2(X16,k3_relat_1(X16))|~v1_relat_1(X16))&(~r1_relat_2(X16,k3_relat_1(X16))|v1_relat_2(X16)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_relat_2])])])).
% 0.12/0.37  cnf(c_0_15, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.37  cnf(c_0_16, plain, (r1_relat_2(X1,X2)|~r2_hidden(k4_tarski(esk2_2(X1,X2),esk2_2(X1,X2)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_17, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_10]), c_0_11])])).
% 0.12/0.37  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.37  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_20, negated_conjecture, ~(![X1]:v1_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t2_wellord2])).
% 0.12/0.37  cnf(c_0_21, plain, (v1_relat_2(X1)|~r1_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_22, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_15]), c_0_11])])).
% 0.12/0.37  cnf(c_0_23, plain, (r1_relat_2(k1_wellord2(X1),X2)|~r2_hidden(esk2_2(k1_wellord2(X1),X2),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_11]), c_0_18])])).
% 0.12/0.37  cnf(c_0_24, plain, (r1_relat_2(k1_wellord2(X1),X2)|r2_hidden(esk2_2(k1_wellord2(X1),X2),X2)), inference(spm,[status(thm)],[c_0_19, c_0_11])).
% 0.12/0.37  fof(c_0_25, negated_conjecture, ~v1_relat_2(k1_wellord2(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.12/0.37  cnf(c_0_26, plain, (v1_relat_2(k1_wellord2(X1))|~r1_relat_2(k1_wellord2(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_11])])).
% 0.12/0.37  cnf(c_0_27, plain, (r1_relat_2(k1_wellord2(X1),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (~v1_relat_2(k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.37  cnf(c_0_29, plain, (v1_relat_2(k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 31
% 0.12/0.37  # Proof object clause steps            : 18
% 0.12/0.37  # Proof object formula steps           : 13
% 0.12/0.37  # Proof object conjectures             : 5
% 0.12/0.37  # Proof object clause conjectures      : 2
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 6
% 0.12/0.37  # Proof object generating inferences   : 5
% 0.12/0.37  # Proof object simplifying inferences  : 15
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 6
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 17
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 17
% 0.12/0.37  # Processed clauses                    : 53
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 51
% 0.12/0.37  # Other redundant clauses eliminated   : 7
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 2
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 30
% 0.12/0.37  # ...of the previous two non-trivial   : 27
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 23
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 7
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 21
% 0.12/0.37  #    Positive orientable unit clauses  : 5
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 0
% 0.12/0.37  #    Non-unit-clauses                  : 16
% 0.12/0.37  # Current number of unprocessed clauses: 6
% 0.12/0.37  # ...number of literals in the above   : 21
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 23
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 132
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 87
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.12/0.37  # Unit Clause-clause subsumption calls : 11
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 7
% 0.12/0.37  # BW rewrite match successes           : 4
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 2046
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.031 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.033 s
% 0.12/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
