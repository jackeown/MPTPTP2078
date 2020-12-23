%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:41 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 180 expanded)
%              Number of clauses        :   25 (  79 expanded)
%              Number of leaves         :    6 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  145 ( 814 expanded)
%              Number of equality atoms :   19 ( 147 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t3_wellord2,conjecture,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v8_relat_2(X11)
        | ~ r2_hidden(k4_tarski(X12,X13),X11)
        | ~ r2_hidden(k4_tarski(X13,X14),X11)
        | r2_hidden(k4_tarski(X12,X14),X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk1_1(X11),esk2_1(X11)),X11)
        | v8_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( r2_hidden(k4_tarski(esk2_1(X11),esk3_1(X11)),X11)
        | v8_relat_2(X11)
        | ~ v1_relat_1(X11) )
      & ( ~ r2_hidden(k4_tarski(esk1_1(X11),esk3_1(X11)),X11)
        | v8_relat_2(X11)
        | ~ v1_relat_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).

fof(c_0_7,plain,(
    ! [X24] : v1_relat_1(k1_wellord2(X24)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X18,X19,X20,X21] :
      ( ( k3_relat_1(X19) = X18
        | X19 != k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X19)
        | r1_tarski(X20,X21)
        | ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X21,X18)
        | X19 != k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r1_tarski(X20,X21)
        | r2_hidden(k4_tarski(X20,X21),X19)
        | ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X21,X18)
        | X19 != k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk4_2(X18,X19),X18)
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(esk5_2(X18,X19),X18)
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X18,X19),esk5_2(X18,X19)),X19)
        | ~ r1_tarski(esk4_2(X18,X19),esk5_2(X18,X19))
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) )
      & ( r2_hidden(k4_tarski(esk4_2(X18,X19),esk5_2(X18,X19)),X19)
        | r1_tarski(esk4_2(X18,X19),esk5_2(X18,X19))
        | k3_relat_1(X19) != X18
        | X19 = k1_wellord2(X18)
        | ~ v1_relat_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,plain,(
    ! [X8,X9,X10] :
      ( ( r2_hidden(X8,k3_relat_1(X10))
        | ~ r2_hidden(k4_tarski(X8,X9),X10)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(X9,k3_relat_1(X10))
        | ~ r2_hidden(k4_tarski(X8,X9),X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_1(X1),esk2_1(X1)),X1)
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

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)
    | v8_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

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
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(k4_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_11])])).

cnf(c_0_18,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_11])).

fof(c_0_19,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]),c_0_11])])).

cnf(c_0_21,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk2_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_22,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk3_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_18]),c_0_17]),c_0_11])])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_25,negated_conjecture,(
    ~ ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t3_wellord2])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r1_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_18]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r2_hidden(esk1_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_16]),c_0_17]),c_0_11])])).

cnf(c_0_29,plain,
    ( v8_relat_2(X1)
    | ~ r2_hidden(k4_tarski(esk1_1(X1),esk3_1(X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_11])])).

fof(c_0_31,negated_conjecture,(
    ~ v8_relat_2(k1_wellord2(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).

cnf(c_0_32,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r1_tarski(X2,esk3_1(k1_wellord2(X1)))
    | ~ r1_tarski(X2,esk2_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_33,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | r1_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_16]),c_0_28]),c_0_21])).

cnf(c_0_34,plain,
    ( v8_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk1_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_11])]),c_0_28]),c_0_22])).

cnf(c_0_35,negated_conjecture,
    ( ~ v8_relat_2(k1_wellord2(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( v8_relat_2(k1_wellord2(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:36:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.027 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(l2_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v8_relat_2(X1)<=>![X2, X3, X4]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X4),X1))=>r2_hidden(k4_tarski(X2,X4),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l2_wellord1)).
% 0.12/0.36  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.12/0.36  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.12/0.36  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.12/0.36  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.12/0.36  fof(t3_wellord2, conjecture, ![X1]:v8_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_wellord2)).
% 0.12/0.36  fof(c_0_6, plain, ![X11, X12, X13, X14]:((~v8_relat_2(X11)|(~r2_hidden(k4_tarski(X12,X13),X11)|~r2_hidden(k4_tarski(X13,X14),X11)|r2_hidden(k4_tarski(X12,X14),X11))|~v1_relat_1(X11))&(((r2_hidden(k4_tarski(esk1_1(X11),esk2_1(X11)),X11)|v8_relat_2(X11)|~v1_relat_1(X11))&(r2_hidden(k4_tarski(esk2_1(X11),esk3_1(X11)),X11)|v8_relat_2(X11)|~v1_relat_1(X11)))&(~r2_hidden(k4_tarski(esk1_1(X11),esk3_1(X11)),X11)|v8_relat_2(X11)|~v1_relat_1(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l2_wellord1])])])])])).
% 0.12/0.36  fof(c_0_7, plain, ![X24]:v1_relat_1(k1_wellord2(X24)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.12/0.36  fof(c_0_8, plain, ![X18, X19, X20, X21]:(((k3_relat_1(X19)=X18|X19!=k1_wellord2(X18)|~v1_relat_1(X19))&((~r2_hidden(k4_tarski(X20,X21),X19)|r1_tarski(X20,X21)|(~r2_hidden(X20,X18)|~r2_hidden(X21,X18))|X19!=k1_wellord2(X18)|~v1_relat_1(X19))&(~r1_tarski(X20,X21)|r2_hidden(k4_tarski(X20,X21),X19)|(~r2_hidden(X20,X18)|~r2_hidden(X21,X18))|X19!=k1_wellord2(X18)|~v1_relat_1(X19))))&(((r2_hidden(esk4_2(X18,X19),X18)|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19))&(r2_hidden(esk5_2(X18,X19),X18)|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19)))&((~r2_hidden(k4_tarski(esk4_2(X18,X19),esk5_2(X18,X19)),X19)|~r1_tarski(esk4_2(X18,X19),esk5_2(X18,X19))|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19))&(r2_hidden(k4_tarski(esk4_2(X18,X19),esk5_2(X18,X19)),X19)|r1_tarski(esk4_2(X18,X19),esk5_2(X18,X19))|k3_relat_1(X19)!=X18|X19=k1_wellord2(X18)|~v1_relat_1(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.12/0.36  fof(c_0_9, plain, ![X8, X9, X10]:((r2_hidden(X8,k3_relat_1(X10))|~r2_hidden(k4_tarski(X8,X9),X10)|~v1_relat_1(X10))&(r2_hidden(X9,k3_relat_1(X10))|~r2_hidden(k4_tarski(X8,X9),X10)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.12/0.36  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_1(X1),esk2_1(X1)),X1)|v8_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.12/0.36  cnf(c_0_12, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_13, plain, (r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)|v8_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  cnf(c_0_15, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_16, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(k4_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.12/0.36  cnf(c_0_17, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_11])])).
% 0.12/0.36  cnf(c_0_18, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_13, c_0_11])).
% 0.12/0.36  fof(c_0_19, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.12/0.36  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_14]), c_0_11])])).
% 0.12/0.36  cnf(c_0_21, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk2_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_11])])).
% 0.12/0.36  cnf(c_0_22, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk3_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_18]), c_0_17]), c_0_11])])).
% 0.12/0.36  cnf(c_0_23, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.36  cnf(c_0_24, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r1_tarski(X1,X2)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.36  fof(c_0_25, negated_conjecture, ~(![X1]:v8_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t3_wellord2])).
% 0.12/0.36  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  cnf(c_0_27, plain, (v8_relat_2(k1_wellord2(X1))|r1_tarski(esk2_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_18]), c_0_21]), c_0_22])).
% 0.12/0.36  cnf(c_0_28, plain, (v8_relat_2(k1_wellord2(X1))|r2_hidden(esk1_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_16]), c_0_17]), c_0_11])])).
% 0.12/0.36  cnf(c_0_29, plain, (v8_relat_2(X1)|~r2_hidden(k4_tarski(esk1_1(X1),esk3_1(X1)),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.12/0.36  cnf(c_0_30, plain, (r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)|~r1_tarski(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_24]), c_0_11])])).
% 0.12/0.36  fof(c_0_31, negated_conjecture, ~v8_relat_2(k1_wellord2(esk6_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_25])])])).
% 0.12/0.36  cnf(c_0_32, plain, (v8_relat_2(k1_wellord2(X1))|r1_tarski(X2,esk3_1(k1_wellord2(X1)))|~r1_tarski(X2,esk2_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.36  cnf(c_0_33, plain, (v8_relat_2(k1_wellord2(X1))|r1_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_16]), c_0_28]), c_0_21])).
% 0.12/0.36  cnf(c_0_34, plain, (v8_relat_2(k1_wellord2(X1))|~r1_tarski(esk1_1(k1_wellord2(X1)),esk3_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_11])]), c_0_28]), c_0_22])).
% 0.12/0.36  cnf(c_0_35, negated_conjecture, (~v8_relat_2(k1_wellord2(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.12/0.36  cnf(c_0_36, plain, (v8_relat_2(k1_wellord2(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])).
% 0.12/0.36  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 38
% 0.12/0.36  # Proof object clause steps            : 25
% 0.12/0.36  # Proof object formula steps           : 13
% 0.12/0.36  # Proof object conjectures             : 5
% 0.12/0.36  # Proof object clause conjectures      : 2
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 11
% 0.12/0.36  # Proof object initial formulas used   : 6
% 0.12/0.36  # Proof object generating inferences   : 10
% 0.12/0.36  # Proof object simplifying inferences  : 29
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 6
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 16
% 0.12/0.36  # Removed in clause preprocessing      : 0
% 0.12/0.36  # Initial clauses in saturation        : 16
% 0.12/0.36  # Processed clauses                    : 51
% 0.12/0.36  # ...of these trivial                  : 0
% 0.12/0.36  # ...subsumed                          : 1
% 0.12/0.36  # ...remaining for further processing  : 50
% 0.12/0.36  # Other redundant clauses eliminated   : 7
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 11
% 0.12/0.36  # Generated clauses                    : 32
% 0.12/0.36  # ...of the previous two non-trivial   : 22
% 0.12/0.36  # Contextual simplify-reflections      : 7
% 0.12/0.36  # Paramodulations                      : 25
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 7
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 16
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 0
% 0.12/0.36  #    Negative unit clauses             : 0
% 0.12/0.36  #    Non-unit-clauses                  : 13
% 0.12/0.36  # Current number of unprocessed clauses: 2
% 0.12/0.36  # ...number of literals in the above   : 10
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 27
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 222
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 83
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 8
% 0.12/0.36  # Unit Clause-clause subsumption calls : 4
% 0.12/0.36  # Rewrite failures with RHS unbound    : 0
% 0.12/0.36  # BW rewrite match attempts            : 3
% 0.12/0.36  # BW rewrite match successes           : 3
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 2327
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.032 s
% 0.12/0.36  # System time              : 0.001 s
% 0.12/0.36  # Total time               : 0.033 s
% 0.12/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
