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
% DateTime   : Thu Dec  3 10:48:35 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 245 expanded)
%              Number of clauses        :   28 ( 105 expanded)
%              Number of leaves         :    7 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 612 expanded)
%              Number of equality atoms :   18 (  98 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t31_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t36_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k4_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(fc2_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))) ) ) ),
    inference(assume_negation,[status(cth)],[t34_relat_1])).

fof(c_0_8,negated_conjecture,
    ( v1_relat_1(esk2_0)
    & v1_relat_1(esk3_0)
    & ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X19,X20)) = k3_xboole_0(X19,X20) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_10,plain,(
    ! [X14,X15,X16] :
      ( ~ r1_tarski(X14,X15)
      | ~ r1_tarski(X14,X16)
      | r1_tarski(X14,k3_xboole_0(X15,X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_11,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k3_relat_1(esk2_0),k4_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_13,c_0_12])).

fof(c_0_16,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ v1_relat_1(X24)
      | ~ r1_tarski(X23,X24)
      | r1_tarski(k3_relat_1(X23),k3_relat_1(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).

fof(c_0_17,plain,(
    ! [X17,X18] : r1_tarski(k4_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t36_xboole_1])).

cnf(c_0_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k3_relat_1(esk3_0))
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k3_relat_1(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( r1_tarski(k3_relat_1(X1),k3_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_relat_1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( ~ v1_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k3_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21])])).

cnf(c_0_23,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_24,plain,(
    ! [X21,X22] :
      ( ~ v1_relat_1(X21)
      | v1_relat_1(k4_xboole_0(X21,X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).

fof(c_0_25,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( r2_hidden(X8,X5)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( r2_hidden(X8,X6)
        | ~ r2_hidden(X8,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X9,X5)
        | ~ r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X7 != k3_xboole_0(X5,X6) )
      & ( ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X10)
        | ~ r2_hidden(esk1_3(X10,X11,X12),X11)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X10)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X11)
        | r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k3_xboole_0(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_26,negated_conjecture,
    ( ~ v1_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_19]),c_0_23])])).

cnf(c_0_27,plain,
    ( v1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_28,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_20])])).

cnf(c_0_30,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_28,c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))
    | r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),X2)
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_3(X1,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))
    | ~ r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))),esk3_0) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | X3 != k4_xboole_0(X4,k4_xboole_0(X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_32,c_0_12])).

cnf(c_0_36,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_33,c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2))) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))
    | ~ r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_37])])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))) = k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_42,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_41]),c_0_29]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.71/0.87  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 0.71/0.87  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.71/0.87  #
% 0.71/0.87  # Preprocessing time       : 0.026 s
% 0.71/0.87  # Presaturation interreduction done
% 0.71/0.87  
% 0.71/0.87  # Proof found!
% 0.71/0.87  # SZS status Theorem
% 0.71/0.87  # SZS output start CNFRefutation
% 0.71/0.87  fof(t34_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 0.71/0.87  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.71/0.87  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.71/0.87  fof(t31_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 0.71/0.87  fof(t36_xboole_1, axiom, ![X1, X2]:r1_tarski(k4_xboole_0(X1,X2),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 0.71/0.87  fof(fc2_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k4_xboole_0(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 0.71/0.87  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.71/0.87  fof(c_0_7, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k3_relat_1(k3_xboole_0(X1,X2)),k3_xboole_0(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t34_relat_1])).
% 0.71/0.87  fof(c_0_8, negated_conjecture, (v1_relat_1(esk2_0)&(v1_relat_1(esk3_0)&~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.71/0.87  fof(c_0_9, plain, ![X19, X20]:k4_xboole_0(X19,k4_xboole_0(X19,X20))=k3_xboole_0(X19,X20), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.71/0.87  fof(c_0_10, plain, ![X14, X15, X16]:(~r1_tarski(X14,X15)|~r1_tarski(X14,X16)|r1_tarski(X14,k3_xboole_0(X15,X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.71/0.87  cnf(c_0_11, negated_conjecture, (~r1_tarski(k3_relat_1(k3_xboole_0(esk2_0,esk3_0)),k3_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.87  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.71/0.87  cnf(c_0_13, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.71/0.87  cnf(c_0_14, negated_conjecture, (~r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(k3_relat_1(esk2_0),k4_xboole_0(k3_relat_1(esk2_0),k3_relat_1(esk3_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 0.71/0.87  cnf(c_0_15, plain, (r1_tarski(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))|~r1_tarski(X1,X3)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_13, c_0_12])).
% 0.71/0.87  fof(c_0_16, plain, ![X23, X24]:(~v1_relat_1(X23)|(~v1_relat_1(X24)|(~r1_tarski(X23,X24)|r1_tarski(k3_relat_1(X23),k3_relat_1(X24))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_relat_1])])])).
% 0.71/0.87  fof(c_0_17, plain, ![X17, X18]:r1_tarski(k4_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t36_xboole_1])).
% 0.71/0.87  cnf(c_0_18, negated_conjecture, (~r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k3_relat_1(esk3_0))|~r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k3_relat_1(esk2_0))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.71/0.87  cnf(c_0_19, plain, (r1_tarski(k3_relat_1(X1),k3_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.71/0.87  cnf(c_0_20, negated_conjecture, (v1_relat_1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.87  cnf(c_0_21, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.71/0.87  cnf(c_0_22, negated_conjecture, (~v1_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))|~r1_tarski(k3_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k3_relat_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21])])).
% 0.71/0.87  cnf(c_0_23, negated_conjecture, (v1_relat_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.71/0.87  fof(c_0_24, plain, ![X21, X22]:(~v1_relat_1(X21)|v1_relat_1(k4_xboole_0(X21,X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc2_relat_1])])).
% 0.71/0.87  fof(c_0_25, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.71/0.87  cnf(c_0_26, negated_conjecture, (~v1_relat_1(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))|~r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_19]), c_0_23])])).
% 0.71/0.87  cnf(c_0_27, plain, (v1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.71/0.87  cnf(c_0_28, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.71/0.87  cnf(c_0_29, negated_conjecture, (~r1_tarski(k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_20])])).
% 0.71/0.87  cnf(c_0_30, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_28, c_0_12])).
% 0.71/0.87  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))|r2_hidden(esk1_3(X1,X2,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),X2)|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk3_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.71/0.87  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.71/0.87  cnf(c_0_33, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.71/0.87  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_3(X1,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))|~r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))),esk3_0)), inference(ef,[status(thm)],[c_0_31])).
% 0.71/0.87  cnf(c_0_35, plain, (r2_hidden(X1,X2)|X3!=k4_xboole_0(X4,k4_xboole_0(X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_32, c_0_12])).
% 0.71/0.87  cnf(c_0_36, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_33, c_0_12])).
% 0.71/0.87  cnf(c_0_37, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 0.71/0.87  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X3,k4_xboole_0(X3,X2)))), inference(er,[status(thm)],[c_0_35])).
% 0.71/0.87  cnf(c_0_39, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))|~r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_37])])).
% 0.71/0.87  cnf(c_0_40, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0)),k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))),esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_37])).
% 0.71/0.87  cnf(c_0_41, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))))=k4_xboole_0(esk2_0,k4_xboole_0(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.71/0.87  cnf(c_0_42, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_41]), c_0_29]), ['proof']).
% 0.71/0.87  # SZS output end CNFRefutation
% 0.71/0.87  # Proof object total steps             : 43
% 0.71/0.87  # Proof object clause steps            : 28
% 0.71/0.87  # Proof object formula steps           : 15
% 0.71/0.87  # Proof object conjectures             : 18
% 0.71/0.87  # Proof object clause conjectures      : 15
% 0.71/0.87  # Proof object formula conjectures     : 3
% 0.71/0.87  # Proof object initial clauses used    : 11
% 0.71/0.87  # Proof object initial formulas used   : 7
% 0.71/0.87  # Proof object generating inferences   : 10
% 0.71/0.87  # Proof object simplifying inferences  : 19
% 0.71/0.87  # Training examples: 0 positive, 0 negative
% 0.71/0.87  # Parsed axioms                        : 7
% 0.71/0.87  # Removed by relevancy pruning/SinE    : 0
% 0.71/0.87  # Initial clauses                      : 14
% 0.71/0.87  # Removed in clause preprocessing      : 1
% 0.71/0.87  # Initial clauses in saturation        : 13
% 0.71/0.87  # Processed clauses                    : 970
% 0.71/0.87  # ...of these trivial                  : 24
% 0.71/0.87  # ...subsumed                          : 434
% 0.71/0.87  # ...remaining for further processing  : 512
% 0.71/0.87  # Other redundant clauses eliminated   : 3
% 0.71/0.87  # Clauses deleted for lack of memory   : 0
% 0.71/0.87  # Backward-subsumed                    : 49
% 0.71/0.87  # Backward-rewritten                   : 7
% 0.71/0.87  # Generated clauses                    : 26123
% 0.71/0.87  # ...of the previous two non-trivial   : 24231
% 0.71/0.87  # Contextual simplify-reflections      : 52
% 0.71/0.87  # Paramodulations                      : 25836
% 0.71/0.87  # Factorizations                       : 284
% 0.71/0.87  # Equation resolutions                 : 3
% 0.71/0.87  # Propositional unsat checks           : 0
% 0.71/0.87  #    Propositional check models        : 0
% 0.71/0.87  #    Propositional check unsatisfiable : 0
% 0.71/0.87  #    Propositional clauses             : 0
% 0.71/0.87  #    Propositional clauses after purity: 0
% 0.71/0.87  #    Propositional unsat core size     : 0
% 0.71/0.87  #    Propositional preprocessing time  : 0.000
% 0.71/0.87  #    Propositional encoding time       : 0.000
% 0.71/0.87  #    Propositional solver time         : 0.000
% 0.71/0.87  #    Success case prop preproc time    : 0.000
% 0.71/0.87  #    Success case prop encoding time   : 0.000
% 0.71/0.87  #    Success case prop solver time     : 0.000
% 0.71/0.87  # Current number of processed clauses  : 440
% 0.71/0.87  #    Positive orientable unit clauses  : 11
% 0.71/0.87  #    Positive unorientable unit clauses: 0
% 0.71/0.87  #    Negative unit clauses             : 4
% 0.71/0.87  #    Non-unit-clauses                  : 425
% 0.71/0.87  # Current number of unprocessed clauses: 23160
% 0.71/0.87  # ...number of literals in the above   : 151209
% 0.71/0.87  # Current number of archived formulas  : 0
% 0.71/0.87  # Current number of archived clauses   : 70
% 0.71/0.87  # Clause-clause subsumption calls (NU) : 30125
% 0.71/0.87  # Rec. Clause-clause subsumption calls : 10216
% 0.71/0.87  # Non-unit clause-clause subsumptions  : 429
% 0.71/0.87  # Unit Clause-clause subsumption calls : 505
% 0.71/0.87  # Rewrite failures with RHS unbound    : 0
% 0.71/0.87  # BW rewrite match attempts            : 28
% 0.71/0.87  # BW rewrite match successes           : 2
% 0.71/0.87  # Condensation attempts                : 0
% 0.71/0.87  # Condensation successes               : 0
% 0.71/0.87  # Termbank termtop insertions          : 725020
% 0.71/0.87  
% 0.71/0.87  # -------------------------------------------------
% 0.71/0.87  # User time                : 0.515 s
% 0.71/0.87  # System time              : 0.013 s
% 0.71/0.87  # Total time               : 0.528 s
% 0.71/0.87  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
