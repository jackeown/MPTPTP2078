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
% DateTime   : Thu Dec  3 10:49:25 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   36 (  74 expanded)
%              Number of clauses        :   21 (  31 expanded)
%              Number of leaves         :    7 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 247 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t74_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t75_relat_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))
      <=> ( r2_hidden(X2,X3)
          & r2_hidden(k4_tarski(X1,X2),X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_relat_1)).

fof(t76_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
        & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(dt_k5_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X2) )
     => v1_relat_1(k5_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(c_0_7,plain,(
    ! [X22,X23,X24,X25] :
      ( ( r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))
        | ~ v1_relat_1(X25) )
      & ( r2_hidden(k4_tarski(X22,X23),X25)
        | ~ r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))
        | ~ v1_relat_1(X25) )
      & ( ~ r2_hidden(X22,X24)
        | ~ r2_hidden(k4_tarski(X22,X23),X25)
        | r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).

fof(c_0_8,plain,(
    ! [X11,X12,X15,X17,X18] :
      ( ( ~ v1_relat_1(X11)
        | ~ r2_hidden(X12,X11)
        | X12 = k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12)) )
      & ( r2_hidden(esk4_1(X15),X15)
        | v1_relat_1(X15) )
      & ( esk4_1(X15) != k4_tarski(X17,X18)
        | v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_9,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( X2 = k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X26,X27,X28,X29] :
      ( ( r2_hidden(X27,X28)
        | ~ r2_hidden(k4_tarski(X26,X27),k5_relat_1(X29,k6_relat_1(X28)))
        | ~ v1_relat_1(X29) )
      & ( r2_hidden(k4_tarski(X26,X27),X29)
        | ~ r2_hidden(k4_tarski(X26,X27),k5_relat_1(X29,k6_relat_1(X28)))
        | ~ v1_relat_1(X29) )
      & ( ~ r2_hidden(X27,X28)
        | ~ r2_hidden(k4_tarski(X26,X27),X29)
        | r2_hidden(k4_tarski(X26,X27),k5_relat_1(X29,k6_relat_1(X28)))
        | ~ v1_relat_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).

cnf(c_0_13,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k5_relat_1(k6_relat_1(X4),X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)
          & r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t76_relat_1])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),X2)
    | r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),X4) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k5_relat_1(X2,k6_relat_1(X4)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & ( ~ r1_tarski(k5_relat_1(esk6_0,k6_relat_1(esk5_0)),esk6_0)
      | ~ r1_tarski(k5_relat_1(k6_relat_1(esk5_0),esk6_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),X2)
    | r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X3)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_17,c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),X1)
    | r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X4)
    | ~ r2_hidden(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),X4) ),
    inference(spm,[status(thm)],[c_0_18,c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_tarski(k5_relat_1(esk6_0,k6_relat_1(esk5_0)),esk6_0)
    | ~ r1_tarski(k5_relat_1(k6_relat_1(esk5_0),esk6_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),X1)
    | r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)
    | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(esk5_0),esk6_0))
    | ~ r1_tarski(k5_relat_1(esk6_0,k6_relat_1(esk5_0)),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_28,plain,
    ( r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)
    | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_26])).

fof(c_0_29,plain,(
    ! [X19,X20] :
      ( ~ v1_relat_1(X19)
      | ~ v1_relat_1(X20)
      | v1_relat_1(k5_relat_1(X19,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).

fof(c_0_30,plain,(
    ! [X21] : v1_relat_1(k6_relat_1(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(esk5_0),esk6_0))
    | ~ v1_relat_1(k5_relat_1(esk6_0,k6_relat_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_25])])).

cnf(c_0_32,plain,
    ( v1_relat_1(k5_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_relat_1(k5_relat_1(esk6_0,k6_relat_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_25]),c_0_33])])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_33]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.12/0.37  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t74_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X3),X4))<=>(r2_hidden(X1,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_relat_1)).
% 0.12/0.37  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.12/0.37  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.37  fof(t75_relat_1, axiom, ![X1, X2, X3, X4]:(v1_relat_1(X4)=>(r2_hidden(k4_tarski(X1,X2),k5_relat_1(X4,k6_relat_1(X3)))<=>(r2_hidden(X2,X3)&r2_hidden(k4_tarski(X1,X2),X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_relat_1)).
% 0.12/0.37  fof(t76_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_relat_1)).
% 0.12/0.37  fof(dt_k5_relat_1, axiom, ![X1, X2]:((v1_relat_1(X1)&v1_relat_1(X2))=>v1_relat_1(k5_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 0.12/0.37  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.12/0.37  fof(c_0_7, plain, ![X22, X23, X24, X25]:(((r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))|~v1_relat_1(X25))&(r2_hidden(k4_tarski(X22,X23),X25)|~r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))|~v1_relat_1(X25)))&(~r2_hidden(X22,X24)|~r2_hidden(k4_tarski(X22,X23),X25)|r2_hidden(k4_tarski(X22,X23),k5_relat_1(k6_relat_1(X24),X25))|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t74_relat_1])])])).
% 0.12/0.37  fof(c_0_8, plain, ![X11, X12, X15, X17, X18]:((~v1_relat_1(X11)|(~r2_hidden(X12,X11)|X12=k4_tarski(esk2_2(X11,X12),esk3_2(X11,X12))))&((r2_hidden(esk4_1(X15),X15)|v1_relat_1(X15))&(esk4_1(X15)!=k4_tarski(X17,X18)|v1_relat_1(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.12/0.37  cnf(c_0_9, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(k6_relat_1(X4),X3))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.37  cnf(c_0_10, plain, (X2=k4_tarski(esk2_2(X1,X2),esk3_2(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  fof(c_0_11, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X26, X27, X28, X29]:(((r2_hidden(X27,X28)|~r2_hidden(k4_tarski(X26,X27),k5_relat_1(X29,k6_relat_1(X28)))|~v1_relat_1(X29))&(r2_hidden(k4_tarski(X26,X27),X29)|~r2_hidden(k4_tarski(X26,X27),k5_relat_1(X29,k6_relat_1(X28)))|~v1_relat_1(X29)))&(~r2_hidden(X27,X28)|~r2_hidden(k4_tarski(X26,X27),X29)|r2_hidden(k4_tarski(X26,X27),k5_relat_1(X29,k6_relat_1(X28)))|~v1_relat_1(X29))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t75_relat_1])])])).
% 0.12/0.37  cnf(c_0_13, plain, (r2_hidden(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r2_hidden(X1,k5_relat_1(k6_relat_1(X4),X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.12/0.37  cnf(c_0_14, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_15, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(k4_tarski(X1,X2),k5_relat_1(X3,k6_relat_1(X4)))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  fof(c_0_16, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k5_relat_1(X2,k6_relat_1(X1)),X2)&r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)))), inference(assume_negation,[status(cth)],[t76_relat_1])).
% 0.12/0.37  cnf(c_0_17, plain, (r2_hidden(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),X2)|r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X3)|~v1_relat_1(X2)|~v1_relat_1(X4)|~r2_hidden(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),X4)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.12/0.37  cnf(c_0_18, plain, (r2_hidden(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X3)|~r2_hidden(X1,k5_relat_1(X2,k6_relat_1(X4)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 0.12/0.37  fof(c_0_19, negated_conjecture, (v1_relat_1(esk6_0)&(~r1_tarski(k5_relat_1(esk6_0,k6_relat_1(esk5_0)),esk6_0)|~r1_tarski(k5_relat_1(k6_relat_1(esk5_0),esk6_0),esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.12/0.37  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_21, plain, (r2_hidden(esk1_2(k5_relat_1(k6_relat_1(X1),X2),X3),X2)|r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X3)|~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_17, c_0_14])).
% 0.12/0.37  cnf(c_0_22, plain, (r2_hidden(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),X1)|r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)|~v1_relat_1(X1)|~v1_relat_1(X4)|~r2_hidden(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),X4)), inference(spm,[status(thm)],[c_0_18, c_0_14])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (~r1_tarski(k5_relat_1(esk6_0,k6_relat_1(esk5_0)),esk6_0)|~r1_tarski(k5_relat_1(k6_relat_1(esk5_0),esk6_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_24, plain, (r1_tarski(k5_relat_1(k6_relat_1(X1),X2),X2)|~v1_relat_1(k5_relat_1(k6_relat_1(X1),X2))|~v1_relat_1(X2)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.37  cnf(c_0_26, plain, (r2_hidden(esk1_2(k5_relat_1(X1,k6_relat_1(X2)),X3),X1)|r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X3)|~v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_14])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (~v1_relat_1(k5_relat_1(k6_relat_1(esk5_0),esk6_0))|~r1_tarski(k5_relat_1(esk6_0,k6_relat_1(esk5_0)),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.12/0.37  cnf(c_0_28, plain, (r1_tarski(k5_relat_1(X1,k6_relat_1(X2)),X1)|~v1_relat_1(k5_relat_1(X1,k6_relat_1(X2)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_26])).
% 0.12/0.37  fof(c_0_29, plain, ![X19, X20]:(~v1_relat_1(X19)|~v1_relat_1(X20)|v1_relat_1(k5_relat_1(X19,X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k5_relat_1])])).
% 0.12/0.37  fof(c_0_30, plain, ![X21]:v1_relat_1(k6_relat_1(X21)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~v1_relat_1(k5_relat_1(k6_relat_1(esk5_0),esk6_0))|~v1_relat_1(k5_relat_1(esk6_0,k6_relat_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_25])])).
% 0.12/0.37  cnf(c_0_32, plain, (v1_relat_1(k5_relat_1(X1,X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_33, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (~v1_relat_1(k5_relat_1(esk6_0,k6_relat_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_25]), c_0_33])])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_32]), c_0_33]), c_0_25])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 36
% 0.12/0.37  # Proof object clause steps            : 21
% 0.12/0.37  # Proof object formula steps           : 15
% 0.12/0.37  # Proof object conjectures             : 9
% 0.12/0.37  # Proof object clause conjectures      : 6
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 9
% 0.12/0.37  # Proof object initial formulas used   : 7
% 0.12/0.37  # Proof object generating inferences   : 12
% 0.12/0.37  # Proof object simplifying inferences  : 10
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 7
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 16
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 16
% 0.12/0.37  # Processed clauses                    : 53
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 7
% 0.12/0.37  # ...remaining for further processing  : 46
% 0.12/0.37  # Other redundant clauses eliminated   : 1
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 0
% 0.12/0.37  # Generated clauses                    : 91
% 0.12/0.37  # ...of the previous two non-trivial   : 79
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 90
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 1
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
% 0.12/0.37  # Current number of processed clauses  : 46
% 0.12/0.37  #    Positive orientable unit clauses  : 3
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 42
% 0.12/0.37  # Current number of unprocessed clauses: 42
% 0.12/0.37  # ...number of literals in the above   : 267
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 0
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 267
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 94
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 7
% 0.12/0.37  # Unit Clause-clause subsumption calls : 4
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 0
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3773
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.005 s
% 0.12/0.37  # Total time               : 0.035 s
% 0.12/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
