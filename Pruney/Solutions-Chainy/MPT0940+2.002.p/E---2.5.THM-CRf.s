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

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 131 expanded)
%              Number of clauses        :   22 (  58 expanded)
%              Number of leaves         :    6 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 581 expanded)
%              Number of equality atoms :   29 ( 127 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   33 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
              & r2_hidden(k4_tarski(X3,X2),X1) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_wellord1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t5_wellord2,conjecture,(
    ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_wellord2)).

fof(c_0_6,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v4_relat_2(X10)
        | ~ r2_hidden(k4_tarski(X11,X12),X10)
        | ~ r2_hidden(k4_tarski(X12,X11),X10)
        | X11 = X12
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk1_1(X10),esk2_1(X10)),X10)
        | v4_relat_2(X10)
        | ~ v1_relat_1(X10) )
      & ( r2_hidden(k4_tarski(esk2_1(X10),esk1_1(X10)),X10)
        | v4_relat_2(X10)
        | ~ v1_relat_1(X10) )
      & ( esk1_1(X10) != esk2_1(X10)
        | v4_relat_2(X10)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).

fof(c_0_7,plain,(
    ! [X21] : v1_relat_1(k1_wellord2(X21)) ),
    inference(variable_rename,[status(thm)],[dt_k1_wellord2])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18] :
      ( ( k3_relat_1(X16) = X15
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(X17,X18),X16)
        | r1_tarski(X17,X18)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X18,X15)
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(X17,X18)
        | r2_hidden(k4_tarski(X17,X18),X16)
        | ~ r2_hidden(X17,X15)
        | ~ r2_hidden(X18,X15)
        | X16 != k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk3_2(X15,X16),X15)
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(esk4_2(X15,X16),X15)
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X16)
        | ~ r1_tarski(esk3_2(X15,X16),esk4_2(X15,X16))
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) )
      & ( r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X16)
        | r1_tarski(esk3_2(X15,X16),esk4_2(X15,X16))
        | k3_relat_1(X16) != X15
        | X16 = k1_wellord2(X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( r2_hidden(X7,k3_relat_1(X9))
        | ~ r2_hidden(k4_tarski(X7,X8),X9)
        | ~ v1_relat_1(X9) )
      & ( r2_hidden(X8,k3_relat_1(X9))
        | ~ r2_hidden(k4_tarski(X7,X8),X9)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).

cnf(c_0_10,plain,
    ( r2_hidden(k4_tarski(esk1_1(X1),esk2_1(X1)),X1)
    | v4_relat_2(X1)
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
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | X3 != k1_wellord2(X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | r2_hidden(k4_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k3_relat_1(k1_wellord2(X1)) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_11])])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,k3_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]),c_0_11])])).

cnf(c_0_20,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | r2_hidden(esk1_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_21,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | r2_hidden(esk2_1(k1_wellord2(X1)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_16]),c_0_11])])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(esk2_1(X1),esk1_1(X1)),X1)
    | v4_relat_2(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | r1_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_15]),c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))),k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_11])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1] : v4_relat_2(k1_wellord2(X1)) ),
    inference(assume_negation,[status(cth)],[t5_wellord2])).

cnf(c_0_27,plain,
    ( esk2_1(k1_wellord2(X1)) = esk1_1(k1_wellord2(X1))
    | v4_relat_2(k1_wellord2(X1))
    | ~ r1_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,plain,
    ( v4_relat_2(k1_wellord2(X1))
    | r1_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_25]),c_0_21]),c_0_20])).

fof(c_0_29,negated_conjecture,(
    ~ v4_relat_2(k1_wellord2(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_30,plain,
    ( v4_relat_2(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,plain,
    ( esk2_1(k1_wellord2(X1)) = esk1_1(k1_wellord2(X1))
    | v4_relat_2(k1_wellord2(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( ~ v4_relat_2(k1_wellord2(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,plain,
    ( v4_relat_2(k1_wellord2(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_11])])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(l3_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>(v4_relat_2(X1)<=>![X2, X3]:((r2_hidden(k4_tarski(X2,X3),X1)&r2_hidden(k4_tarski(X3,X2),X1))=>X2=X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_wellord1)).
% 0.20/0.38  fof(dt_k1_wellord2, axiom, ![X1]:v1_relat_1(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 0.20/0.38  fof(d1_wellord2, axiom, ![X1, X2]:(v1_relat_1(X2)=>(X2=k1_wellord2(X1)<=>(k3_relat_1(X2)=X1&![X3, X4]:((r2_hidden(X3,X1)&r2_hidden(X4,X1))=>(r2_hidden(k4_tarski(X3,X4),X2)<=>r1_tarski(X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 0.20/0.38  fof(t30_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 0.20/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.38  fof(t5_wellord2, conjecture, ![X1]:v4_relat_2(k1_wellord2(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_wellord2)).
% 0.20/0.38  fof(c_0_6, plain, ![X10, X11, X12]:((~v4_relat_2(X10)|(~r2_hidden(k4_tarski(X11,X12),X10)|~r2_hidden(k4_tarski(X12,X11),X10)|X11=X12)|~v1_relat_1(X10))&(((r2_hidden(k4_tarski(esk1_1(X10),esk2_1(X10)),X10)|v4_relat_2(X10)|~v1_relat_1(X10))&(r2_hidden(k4_tarski(esk2_1(X10),esk1_1(X10)),X10)|v4_relat_2(X10)|~v1_relat_1(X10)))&(esk1_1(X10)!=esk2_1(X10)|v4_relat_2(X10)|~v1_relat_1(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_wellord1])])])])])).
% 0.20/0.38  fof(c_0_7, plain, ![X21]:v1_relat_1(k1_wellord2(X21)), inference(variable_rename,[status(thm)],[dt_k1_wellord2])).
% 0.20/0.38  fof(c_0_8, plain, ![X15, X16, X17, X18]:(((k3_relat_1(X16)=X15|X16!=k1_wellord2(X15)|~v1_relat_1(X16))&((~r2_hidden(k4_tarski(X17,X18),X16)|r1_tarski(X17,X18)|(~r2_hidden(X17,X15)|~r2_hidden(X18,X15))|X16!=k1_wellord2(X15)|~v1_relat_1(X16))&(~r1_tarski(X17,X18)|r2_hidden(k4_tarski(X17,X18),X16)|(~r2_hidden(X17,X15)|~r2_hidden(X18,X15))|X16!=k1_wellord2(X15)|~v1_relat_1(X16))))&(((r2_hidden(esk3_2(X15,X16),X15)|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16))&(r2_hidden(esk4_2(X15,X16),X15)|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16)))&((~r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X16)|~r1_tarski(esk3_2(X15,X16),esk4_2(X15,X16))|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16))&(r2_hidden(k4_tarski(esk3_2(X15,X16),esk4_2(X15,X16)),X16)|r1_tarski(esk3_2(X15,X16),esk4_2(X15,X16))|k3_relat_1(X16)!=X15|X16=k1_wellord2(X15)|~v1_relat_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord2])])])])])).
% 0.20/0.38  fof(c_0_9, plain, ![X7, X8, X9]:((r2_hidden(X7,k3_relat_1(X9))|~r2_hidden(k4_tarski(X7,X8),X9)|~v1_relat_1(X9))&(r2_hidden(X8,k3_relat_1(X9))|~r2_hidden(k4_tarski(X7,X8),X9)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_relat_1])])])).
% 0.20/0.38  cnf(c_0_10, plain, (r2_hidden(k4_tarski(esk1_1(X1),esk2_1(X1)),X1)|v4_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_11, plain, (v1_relat_1(k1_wellord2(X1))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, plain, (k3_relat_1(X1)=X2|X1!=k1_wellord2(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_13, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|~r2_hidden(X2,X4)|X3!=k1_wellord2(X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  cnf(c_0_14, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  cnf(c_0_15, plain, (v4_relat_2(k1_wellord2(X1))|r2_hidden(k4_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.38  cnf(c_0_16, plain, (k3_relat_1(k1_wellord2(X1))=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_11])])).
% 0.20/0.38  cnf(c_0_17, plain, (r2_hidden(X1,k3_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.38  fof(c_0_18, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.38  cnf(c_0_19, plain, (r1_tarski(X1,X2)|~r2_hidden(k4_tarski(X1,X2),k1_wellord2(X3))|~r2_hidden(X2,X3)|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_13]), c_0_11])])).
% 0.20/0.38  cnf(c_0_20, plain, (v4_relat_2(k1_wellord2(X1))|r2_hidden(esk1_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_11])])).
% 0.20/0.38  cnf(c_0_21, plain, (v4_relat_2(k1_wellord2(X1))|r2_hidden(esk2_1(k1_wellord2(X1)),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_16]), c_0_11])])).
% 0.20/0.38  cnf(c_0_22, plain, (r2_hidden(k4_tarski(esk2_1(X1),esk1_1(X1)),X1)|v4_relat_2(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.38  cnf(c_0_24, plain, (v4_relat_2(k1_wellord2(X1))|r1_tarski(esk1_1(k1_wellord2(X1)),esk2_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_15]), c_0_20]), c_0_21])).
% 0.20/0.38  cnf(c_0_25, plain, (v4_relat_2(k1_wellord2(X1))|r2_hidden(k4_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1))),k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_22, c_0_11])).
% 0.20/0.38  fof(c_0_26, negated_conjecture, ~(![X1]:v4_relat_2(k1_wellord2(X1))), inference(assume_negation,[status(cth)],[t5_wellord2])).
% 0.20/0.38  cnf(c_0_27, plain, (esk2_1(k1_wellord2(X1))=esk1_1(k1_wellord2(X1))|v4_relat_2(k1_wellord2(X1))|~r1_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.38  cnf(c_0_28, plain, (v4_relat_2(k1_wellord2(X1))|r1_tarski(esk2_1(k1_wellord2(X1)),esk1_1(k1_wellord2(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_25]), c_0_21]), c_0_20])).
% 0.20/0.38  fof(c_0_29, negated_conjecture, ~v4_relat_2(k1_wellord2(esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.20/0.38  cnf(c_0_30, plain, (v4_relat_2(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.38  cnf(c_0_31, plain, (esk2_1(k1_wellord2(X1))=esk1_1(k1_wellord2(X1))|v4_relat_2(k1_wellord2(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.38  cnf(c_0_32, negated_conjecture, (~v4_relat_2(k1_wellord2(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.38  cnf(c_0_33, plain, (v4_relat_2(k1_wellord2(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_11])])).
% 0.20/0.38  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33])]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 35
% 0.20/0.38  # Proof object clause steps            : 22
% 0.20/0.38  # Proof object formula steps           : 13
% 0.20/0.38  # Proof object conjectures             : 5
% 0.20/0.38  # Proof object clause conjectures      : 2
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 10
% 0.20/0.38  # Proof object initial formulas used   : 6
% 0.20/0.38  # Proof object generating inferences   : 9
% 0.20/0.38  # Proof object simplifying inferences  : 20
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 6
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 18
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 18
% 0.20/0.38  # Processed clauses                    : 56
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 3
% 0.20/0.38  # ...remaining for further processing  : 53
% 0.20/0.38  # Other redundant clauses eliminated   : 9
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 1
% 0.20/0.38  # Backward-rewritten                   : 9
% 0.20/0.38  # Generated clauses                    : 39
% 0.20/0.38  # ...of the previous two non-trivial   : 26
% 0.20/0.38  # Contextual simplify-reflections      : 4
% 0.20/0.38  # Paramodulations                      : 30
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 9
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
% 0.20/0.38  # Current number of processed clauses  : 17
% 0.20/0.38  #    Positive orientable unit clauses  : 4
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 0
% 0.20/0.38  #    Non-unit-clauses                  : 13
% 0.20/0.38  # Current number of unprocessed clauses: 4
% 0.20/0.38  # ...number of literals in the above   : 9
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 27
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 194
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 104
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.20/0.38  # Unit Clause-clause subsumption calls : 4
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 3
% 0.20/0.38  # BW rewrite match successes           : 3
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 2330
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.033 s
% 0.20/0.38  # System time              : 0.002 s
% 0.20/0.38  # Total time               : 0.035 s
% 0.20/0.38  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
