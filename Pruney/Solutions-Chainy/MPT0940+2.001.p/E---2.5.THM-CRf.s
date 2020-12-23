%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:00:41 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   40 (  92 expanded)
%              Number of clauses        :   27 (  43 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  160 ( 464 expanded)
%              Number of equality atoms :   29 (  76 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(dt_k1_wellord2,axiom,(
    ! [X1] : v1_relat_1(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(d4_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r4_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(k4_tarski(X4,X3),X1) )
             => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d12_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> r4_relat_2(X1,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(t5_wellord2,conjecture,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

fof(c_0_6,plain,(
    ! [X8,X9,X10,X11] :
      ( ( k3_relat_1(X9) = X8
        | X9 != k1_wellord2(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(X10,X11),X9)
        | r1_tarski(X10,X11)
        | ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X11,X8)
        | X9 != k1_wellord2(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(X10,X11)
        | r2_hidden(k4_tarski(X10,X11),X9)
        | ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X11,X8)
        | X9 != k1_wellord2(X8)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | k3_relat_1(X9) != X8
        | X9 = k1_wellord2(X8)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(esk2_2(X8,X9),X8)
        | k3_relat_1(X9) != X8
        | X9 = k1_wellord2(X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X8,X9),esk2_2(X8,X9)),X9)
        | ~ r1_tarski(esk1_2(X8,X9),esk2_2(X8,X9))
        | k3_relat_1(X9) != X8
        | X9 = k1_wellord2(X8)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(k4_tarski(esk1_2(X8,X9),esk2_2(X8,X9)),X9)
        | r1_tarski(esk1_2(X8,X9),esk2_2(X8,X9))
        | k3_relat_1(X9) != X8
        | X9 = k1_wellord2(X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_7,plain,(
    ! [X21] : v1_relat_1(k1_wellord2(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( ~ r4_relat_2(X14,X15)
        | ~ r2_hidden(X16,X15)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(k4_tarski(X16,X17),X14)
        | ~ r2_hidden(k4_tarski(X17,X16),X14)
        | X16 = X17
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk3_2(X14,X18),X18)
        | r4_relat_2(X14,X18)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk4_2(X14,X18),X18)
        | r4_relat_2(X14,X18)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk3_2(X14,X18),esk4_2(X14,X18)),X14)
        | r4_relat_2(X14,X18)
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk4_2(X14,X18),esk3_2(X14,X18)),X14)
        | r4_relat_2(X14,X18)
        | ~ v1_relat_1(X14) )
      & ( esk3_2(X14,X18) != esk4_2(X14,X18)
        | r4_relat_2(X14,X18)
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).

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
    ( r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]),c_0_10])])).

cnf(c_0_13,plain,
    ( r2_hidden(k4_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1))
    | r4_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)
    | r4_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_17,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_18,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r1_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk4_2(k1_wellord2(X1),X2),X2)
    | r4_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_14,c_0_10])).

cnf(c_0_20,plain,
    ( r2_hidden(esk3_2(k1_wellord2(X1),X2),X2)
    | r4_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2)),k1_wellord2(X1))
    | r4_relat_2(k1_wellord2(X1),X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r4_relat_2(k1_wellord2(X1),X1)
    | r1_tarski(esk3_2(k1_wellord2(X1),X1),esk4_2(k1_wellord2(X1),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_24,plain,
    ( r4_relat_2(k1_wellord2(X1),X2)
    | r1_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2))
    | ~ r2_hidden(esk3_2(k1_wellord2(X1),X2),X1)
    | ~ r2_hidden(esk4_2(k1_wellord2(X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_21])).

fof(c_0_25,plain,(
    ! [X7] :
      ( ( ~ v4_relat_2(X7)
        | r4_relat_2(X7,k3_relat_1(X7))
        | ~ v1_relat_1(X7) )
      & ( ~ r4_relat_2(X7,k3_relat_1(X7))
        | v4_relat_2(X7)
        | ~ v1_relat_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).

cnf(c_0_26,plain,
    ( k3_relat_1(X1) = X2
    | X1 != k1_wellord2(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( esk4_2(k1_wellord2(X1),X1) = esk3_2(k1_wellord2(X1),X1)
    | r4_relat_2(k1_wellord2(X1),X1)
    | ~ r1_tarski(esk4_2(k1_wellord2(X1),X1),esk3_2(k1_wellord2(X1),X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,plain,
    ( r4_relat_2(k1_wellord2(X1),X1)
    | r1_tarski(esk4_2(k1_wellord2(X1),X1),esk3_2(k1_wellord2(X1),X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_20]),c_0_19])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t5_wellord2])).

cnf(c_0_30,plain,
    ( v4_relat_2(X1)
    | ~ r4_relat_2(X1,k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_10])])).

cnf(c_0_32,plain,
    ( r4_relat_2(X1,X2)
    | esk3_2(X1,X2) != esk4_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,plain,
    ( esk4_2(k1_wellord2(X1),X1) = esk3_2(k1_wellord2(X1),X1)
    | r4_relat_2(k1_wellord2(X1),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_34,negated_conjecture,(
    ~ v4_relat_2(k1_wellord2(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

cnf(c_0_35,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | ~ r4_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_10])])).

cnf(c_0_36,plain,
    ( r4_relat_2(k1_wellord2(X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_10])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v4_relat_2(k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,plain,
    ( v4_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_39,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:19:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.027 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 0.14/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.14/0.38  fof(d4_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r4_relat_2(X1,X2)<=>![X3, X4]:((((r2_hidden(X3,X2)&r2_hidden(X4,X2))&r2_hidden(k4_tarski(X3,X4),X1))&r2_hidden(k4_tarski(X4,X3),X1))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_2)).
% 0.14/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.38  fof(d12_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>r4_relat_2(X1,k3_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_2)).
% 0.14/0.38  fof(t5_wellord2, conjecture, ![X1]:v4_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_wellord2)).
% 0.14/0.38  fof(c_0_6, plain, ![X8, X9, X10, X11]:(((k3_relat_1(X9)=X8|X9!=k1_wellord2(X8)|~v1_relat_1(X9))&((~r2_hidden(k4_tarski(X10,X11),X9)|r1_tarski(X10,X11)|(~r2_hidden(X10,X8)|~r2_hidden(X11,X8))|X9!=k1_wellord2(X8)|~v1_relat_1(X9))&(~r1_tarski(X10,X11)|r2_hidden(k4_tarski(X10,X11),X9)|(~r2_hidden(X10,X8)|~r2_hidden(X11,X8))|X9!=k1_wellord2(X8)|~v1_relat_1(X9))))&(((r2_hidden(esk1_2(X8,X9),X8)|k3_relat_1(X9)!=X8|X9=k1_wellord2(X8)|~v1_relat_1(X9))&(r2_hidden(esk2_2(X8,X9),X8)|k3_relat_1(X9)!=X8|X9=k1_wellord2(X8)|~v1_relat_1(X9)))&((~r2_hidden(k4_tarski(esk1_2(X8,X9),esk2_2(X8,X9)),X9)|~r1_tarski(esk1_2(X8,X9),esk2_2(X8,X9))|k3_relat_1(X9)!=X8|X9=k1_wellord2(X8)|~v1_relat_1(X9))&(r2_hidden(k4_tarski(esk1_2(X8,X9),esk2_2(X8,X9)),X9)|r1_tarski(esk1_2(X8,X9),esk2_2(X8,X9))|k3_relat_1(X9)!=X8|X9=k1_wellord2(X8)|~v1_relat_1(X9))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.14/0.38  fof(c_0_7, plain, ![X21]:v1_relat_1(k1_wellord2(X21)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.14/0.38  fof(c_0_8, plain, ![X14, X15, X16, X17, X18]:((~r4_relat_2(X14,X15)|(~r2_hidden(X16,X15)|~r2_hidden(X17,X15)|~r2_hidden(k4_tarski(X16,X17),X14)|~r2_hidden(k4_tarski(X17,X16),X14)|X16=X17)|~v1_relat_1(X14))&(((((r2_hidden(esk3_2(X14,X18),X18)|r4_relat_2(X14,X18)|~v1_relat_1(X14))&(r2_hidden(esk4_2(X14,X18),X18)|r4_relat_2(X14,X18)|~v1_relat_1(X14)))&(r2_hidden(k4_tarski(esk3_2(X14,X18),esk4_2(X14,X18)),X14)|r4_relat_2(X14,X18)|~v1_relat_1(X14)))&(r2_hidden(k4_tarski(esk4_2(X14,X18),esk3_2(X14,X18)),X14)|r4_relat_2(X14,X18)|~v1_relat_1(X14)))&(esk3_2(X14,X18)!=esk4_2(X14,X18)|r4_relat_2(X14,X18)|~v1_relat_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_2])])])])])])).
% 0.14/0.38  cnf(c_0_9, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_10, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.38  cnf(c_0_11, plain, (r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|r4_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_12, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_9]), c_0_10])])).
% 0.14/0.38  cnf(c_0_13, plain, (r2_hidden(k4_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2)),k1_wellord2(X1))|r4_relat_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_11, c_0_10])).
% 0.14/0.38  cnf(c_0_14, plain, (r2_hidden(esk4_2(X1,X2),X2)|r4_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_15, plain, (r2_hidden(esk3_2(X1,X2),X2)|r4_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_16, plain, (r2_hidden(k4_tarski(esk4_2(X1,X2),esk3_2(X1,X2)),X1)|r4_relat_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  fof(c_0_17, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.38  cnf(c_0_18, plain, (r4_relat_2(k1_wellord2(X1),X2)|r1_tarski(esk3_2(k1_wellord2(X1),X2),esk4_2(k1_wellord2(X1),X2))|~r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)|~r2_hidden(esk3_2(k1_wellord2(X1),X2),X1)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.38  cnf(c_0_19, plain, (r2_hidden(esk4_2(k1_wellord2(X1),X2),X2)|r4_relat_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_14, c_0_10])).
% 0.14/0.38  cnf(c_0_20, plain, (r2_hidden(esk3_2(k1_wellord2(X1),X2),X2)|r4_relat_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_15, c_0_10])).
% 0.14/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2)),k1_wellord2(X1))|r4_relat_2(k1_wellord2(X1),X2)), inference(spm,[status(thm)],[c_0_16, c_0_10])).
% 0.14/0.38  cnf(c_0_22, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.38  cnf(c_0_23, plain, (r4_relat_2(k1_wellord2(X1),X1)|r1_tarski(esk3_2(k1_wellord2(X1),X1),esk4_2(k1_wellord2(X1),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 0.14/0.38  cnf(c_0_24, plain, (r4_relat_2(k1_wellord2(X1),X2)|r1_tarski(esk4_2(k1_wellord2(X1),X2),esk3_2(k1_wellord2(X1),X2))|~r2_hidden(esk3_2(k1_wellord2(X1),X2),X1)|~r2_hidden(esk4_2(k1_wellord2(X1),X2),X1)), inference(spm,[status(thm)],[c_0_12, c_0_21])).
% 0.14/0.38  fof(c_0_25, plain, ![X7]:((~v4_relat_2(X7)|r4_relat_2(X7,k3_relat_1(X7))|~v1_relat_1(X7))&(~r4_relat_2(X7,k3_relat_1(X7))|v4_relat_2(X7)|~v1_relat_1(X7))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_2])])])).
% 0.14/0.38  cnf(c_0_26, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.38  cnf(c_0_27, plain, (esk4_2(k1_wellord2(X1),X1)=esk3_2(k1_wellord2(X1),X1)|r4_relat_2(k1_wellord2(X1),X1)|~r1_tarski(esk4_2(k1_wellord2(X1),X1),esk3_2(k1_wellord2(X1),X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_28, plain, (r4_relat_2(k1_wellord2(X1),X1)|r1_tarski(esk4_2(k1_wellord2(X1),X1),esk3_2(k1_wellord2(X1),X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_20]), c_0_19])).
% 0.14/0.38  fof(c_0_29, negated_conjecture, ~(![X1]:v4_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t5_wellord2])).
% 0.14/0.38  cnf(c_0_30, plain, (v4_relat_2(X1)|~r4_relat_2(X1,k3_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_31, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_10])])).
% 0.14/0.38  cnf(c_0_32, plain, (r4_relat_2(X1,X2)|esk3_2(X1,X2)!=esk4_2(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.38  cnf(c_0_33, plain, (esk4_2(k1_wellord2(X1),X1)=esk3_2(k1_wellord2(X1),X1)|r4_relat_2(k1_wellord2(X1),X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  fof(c_0_34, negated_conjecture, ~v4_relat_2(k1_wellord2(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.14/0.38  cnf(c_0_35, plain, (v4_relat_2(k1_wellord2(X1))|~r4_relat_2(k1_wellord2(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_10])])).
% 0.14/0.38  cnf(c_0_36, plain, (r4_relat_2(k1_wellord2(X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_10])])).
% 0.14/0.38  cnf(c_0_37, negated_conjecture, (~v4_relat_2(k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_38, plain, (v4_relat_2(k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_36])])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_38])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 40
% 0.14/0.38  # Proof object clause steps            : 27
% 0.14/0.38  # Proof object formula steps           : 13
% 0.14/0.38  # Proof object conjectures             : 5
% 0.14/0.38  # Proof object clause conjectures      : 2
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 11
% 0.14/0.38  # Proof object initial formulas used   : 6
% 0.14/0.38  # Proof object generating inferences   : 12
% 0.14/0.38  # Proof object simplifying inferences  : 16
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 6
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 20
% 0.14/0.38  # Removed in clause preprocessing      : 0
% 0.14/0.38  # Initial clauses in saturation        : 20
% 0.14/0.38  # Processed clauses                    : 64
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 1
% 0.14/0.38  # ...remaining for further processing  : 63
% 0.14/0.38  # Other redundant clauses eliminated   : 9
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 6
% 0.14/0.38  # Generated clauses                    : 42
% 0.14/0.38  # ...of the previous two non-trivial   : 32
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 33
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 9
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 28
% 0.14/0.38  #    Positive orientable unit clauses  : 5
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 23
% 0.14/0.38  # Current number of unprocessed clauses: 7
% 0.14/0.38  # ...number of literals in the above   : 31
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 26
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 219
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 121
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.38  # Unit Clause-clause subsumption calls : 18
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 5
% 0.14/0.38  # BW rewrite match successes           : 2
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 2696
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.031 s
% 0.14/0.38  # System time              : 0.004 s
% 0.14/0.38  # Total time               : 0.034 s
% 0.14/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
