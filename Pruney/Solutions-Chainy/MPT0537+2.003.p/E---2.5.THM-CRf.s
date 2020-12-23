%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 142 expanded)
%              Number of clauses        :   31 (  68 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  147 ( 398 expanded)
%              Number of equality atoms :   48 ( 151 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t137_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(t127_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k8_relat_1(X1,k8_relat_1(X2,X3)) = k8_relat_1(k3_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_relat_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(d12_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( X3 = k8_relat_1(X1,X2)
          <=> ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X3)
              <=> ( r2_hidden(X5,X1)
                  & r2_hidden(k4_tarski(X4,X5),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(dt_k8_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => v1_relat_1(k8_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(c_0_10,plain,(
    ! [X15] : k3_xboole_0(X15,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_11,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k3_xboole_0(X17,X18) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(k1_xboole_0,X1) = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t137_relat_1])).

fof(c_0_13,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_relat_1(X33)
      | k8_relat_1(X31,k8_relat_1(X32,X33)) = k8_relat_1(k3_xboole_0(X31,X32),X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).

fof(c_0_14,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( r2_hidden(X9,X6)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X9,X7)
        | ~ r2_hidden(X9,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k4_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k4_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k4_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

cnf(c_0_15,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_17,plain,(
    ! [X16] : k4_xboole_0(X16,k1_xboole_0) = X16 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_18,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26] :
      ( ( r2_hidden(X24,X20)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k8_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(X23,X24),X21)
        | ~ r2_hidden(k4_tarski(X23,X24),X22)
        | X22 != k8_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(X26,X20)
        | ~ r2_hidden(k4_tarski(X25,X26),X21)
        | r2_hidden(k4_tarski(X25,X26),X22)
        | X22 != k8_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( ~ r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X22)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X21)
        | X22 = k8_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X22)
        | X22 = k8_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) )
      & ( r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X21)
        | r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X22)
        | X22 = k8_relat_1(X20,X21)
        | ~ v1_relat_1(X22)
        | ~ v1_relat_1(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).

fof(c_0_19,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | v1_relat_1(k8_relat_1(X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & k8_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

cnf(c_0_21,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k3_xboole_0(X2,X3),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_23,plain,(
    ! [X19] : k4_xboole_0(k1_xboole_0,X19) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),X4)
    | X4 != k8_relat_1(X2,X5)
    | ~ v1_relat_1(X4)
    | ~ v1_relat_1(X5) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_relat_1(k8_relat_1(X2,X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( k8_relat_1(X2,k8_relat_1(X3,X1)) = k8_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_35,plain,(
    ! [X34] :
      ( ~ v1_relat_1(X34)
      | r2_hidden(k4_tarski(esk4_1(X34),esk5_1(X34)),X34)
      | X34 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(k4_tarski(X4,X1),k8_relat_1(X2,X3)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(k8_relat_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk6_0) = k8_relat_1(X1,k8_relat_1(X2,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,esk6_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_3(X2,X2,X1),X2)
    | r2_hidden(esk1_3(X2,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(esk4_1(X1),esk5_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,k8_relat_1(X4,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( k8_relat_1(k1_xboole_0,k8_relat_1(X1,esk6_0)) = k8_relat_1(k1_xboole_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_32])).

cnf(c_0_46,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,X2),X2)
    | r2_hidden(esk1_3(X1,X1,X2),X1)
    | k8_relat_1(X2,esk6_0) != X2 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k8_relat_1(X1,esk6_0) = k1_xboole_0
    | r2_hidden(k4_tarski(esk4_1(k8_relat_1(X1,esk6_0)),esk5_1(k8_relat_1(X1,esk6_0))),k8_relat_1(X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,X2),k8_relat_1(k1_xboole_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_3(X1,X1,k1_xboole_0),X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48])]),c_0_46]),c_0_49])).

cnf(c_0_51,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_46,c_0_50]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:36:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.42  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.42  # and selection function SelectNegativeLiterals.
% 0.13/0.42  #
% 0.13/0.42  # Preprocessing time       : 0.027 s
% 0.13/0.42  # Presaturation interreduction done
% 0.13/0.42  
% 0.13/0.42  # Proof found!
% 0.13/0.42  # SZS status Theorem
% 0.13/0.42  # SZS output start CNFRefutation
% 0.13/0.42  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.13/0.42  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.13/0.42  fof(t137_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 0.13/0.42  fof(t127_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k8_relat_1(X1,k8_relat_1(X2,X3))=k8_relat_1(k3_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_relat_1)).
% 0.13/0.42  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.13/0.42  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.13/0.42  fof(d12_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(X3=k8_relat_1(X1,X2)<=>![X4, X5]:(r2_hidden(k4_tarski(X4,X5),X3)<=>(r2_hidden(X5,X1)&r2_hidden(k4_tarski(X4,X5),X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 0.13/0.42  fof(dt_k8_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>v1_relat_1(k8_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 0.13/0.42  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.13/0.42  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.13/0.42  fof(c_0_10, plain, ![X15]:k3_xboole_0(X15,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.13/0.42  fof(c_0_11, plain, ![X17, X18]:k4_xboole_0(X17,k4_xboole_0(X17,X18))=k3_xboole_0(X17,X18), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.13/0.42  fof(c_0_12, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>k8_relat_1(k1_xboole_0,X1)=k1_xboole_0)), inference(assume_negation,[status(cth)],[t137_relat_1])).
% 0.13/0.42  fof(c_0_13, plain, ![X31, X32, X33]:(~v1_relat_1(X33)|k8_relat_1(X31,k8_relat_1(X32,X33))=k8_relat_1(k3_xboole_0(X31,X32),X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t127_relat_1])])).
% 0.13/0.42  fof(c_0_14, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:((((r2_hidden(X9,X6)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7))&(~r2_hidden(X9,X7)|~r2_hidden(X9,X8)|X8!=k4_xboole_0(X6,X7)))&(~r2_hidden(X10,X6)|r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k4_xboole_0(X6,X7)))&((~r2_hidden(esk1_3(X11,X12,X13),X13)|(~r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k4_xboole_0(X11,X12))&((r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k4_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.13/0.42  cnf(c_0_15, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.42  cnf(c_0_16, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.42  fof(c_0_17, plain, ![X16]:k4_xboole_0(X16,k1_xboole_0)=X16, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.13/0.42  fof(c_0_18, plain, ![X20, X21, X22, X23, X24, X25, X26]:((((r2_hidden(X24,X20)|~r2_hidden(k4_tarski(X23,X24),X22)|X22!=k8_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r2_hidden(k4_tarski(X23,X24),X21)|~r2_hidden(k4_tarski(X23,X24),X22)|X22!=k8_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)))&(~r2_hidden(X26,X20)|~r2_hidden(k4_tarski(X25,X26),X21)|r2_hidden(k4_tarski(X25,X26),X22)|X22!=k8_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21)))&((~r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X22)|(~r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X21))|X22=k8_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21))&((r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X22)|X22=k8_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21))&(r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X21)|r2_hidden(k4_tarski(esk2_3(X20,X21,X22),esk3_3(X20,X21,X22)),X22)|X22=k8_relat_1(X20,X21)|~v1_relat_1(X22)|~v1_relat_1(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_relat_1])])])])])])).
% 0.13/0.42  fof(c_0_19, plain, ![X29, X30]:(~v1_relat_1(X30)|v1_relat_1(k8_relat_1(X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relat_1])])).
% 0.13/0.42  fof(c_0_20, negated_conjecture, (v1_relat_1(esk6_0)&k8_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).
% 0.13/0.42  cnf(c_0_21, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k3_xboole_0(X2,X3),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.42  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.42  fof(c_0_23, plain, ![X19]:k4_xboole_0(k1_xboole_0,X19)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.13/0.42  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.42  cnf(c_0_25, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.42  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),X4)|X4!=k8_relat_1(X2,X5)|~v1_relat_1(X4)|~v1_relat_1(X5)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.42  cnf(c_0_27, plain, (v1_relat_1(k8_relat_1(X2,X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.42  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.42  cnf(c_0_29, plain, (k8_relat_1(X2,k8_relat_1(X3,X1))=k8_relat_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_21, c_0_16])).
% 0.13/0.42  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.42  cnf(c_0_31, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_22])).
% 0.13/0.42  cnf(c_0_32, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.42  cnf(c_0_33, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.42  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.42  fof(c_0_35, plain, ![X34]:(~v1_relat_1(X34)|(r2_hidden(k4_tarski(esk4_1(X34),esk5_1(X34)),X34)|X34=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.13/0.42  cnf(c_0_36, plain, (r2_hidden(X1,X2)|~v1_relat_1(X3)|~r2_hidden(k4_tarski(X4,X1),k8_relat_1(X2,X3))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_27])).
% 0.13/0.42  cnf(c_0_37, negated_conjecture, (v1_relat_1(k8_relat_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.42  cnf(c_0_38, negated_conjecture, (k8_relat_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),esk6_0)=k8_relat_1(X1,k8_relat_1(X2,esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.13/0.42  cnf(c_0_39, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_30])).
% 0.13/0.42  cnf(c_0_40, plain, (~r2_hidden(X1,k1_xboole_0)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.42  cnf(c_0_41, negated_conjecture, (k8_relat_1(k1_xboole_0,esk6_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.42  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk1_3(X2,X2,X1),X2)|r2_hidden(esk1_3(X2,X2,X1),X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.42  cnf(c_0_43, plain, (r2_hidden(k4_tarski(esk4_1(X1),esk5_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.13/0.42  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k8_relat_1(X2,k8_relat_1(X4,esk6_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.42  cnf(c_0_45, negated_conjecture, (k8_relat_1(k1_xboole_0,k8_relat_1(X1,esk6_0))=k8_relat_1(k1_xboole_0,esk6_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_32]), c_0_32])).
% 0.13/0.42  cnf(c_0_46, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_33]), c_0_40])).
% 0.13/0.42  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_3(X1,X1,X2),X2)|r2_hidden(esk1_3(X1,X1,X2),X1)|k8_relat_1(X2,esk6_0)!=X2), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.42  cnf(c_0_48, negated_conjecture, (k8_relat_1(X1,esk6_0)=k1_xboole_0|r2_hidden(k4_tarski(esk4_1(k8_relat_1(X1,esk6_0)),esk5_1(k8_relat_1(X1,esk6_0))),k8_relat_1(X1,esk6_0))), inference(spm,[status(thm)],[c_0_43, c_0_37])).
% 0.13/0.42  cnf(c_0_49, negated_conjecture, (~r2_hidden(k4_tarski(X1,X2),k8_relat_1(k1_xboole_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])).
% 0.13/0.42  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_3(X1,X1,k1_xboole_0),X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48])]), c_0_46]), c_0_49])).
% 0.13/0.42  cnf(c_0_51, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_46, c_0_50]), ['proof']).
% 0.13/0.42  # SZS output end CNFRefutation
% 0.13/0.42  # Proof object total steps             : 52
% 0.13/0.42  # Proof object clause steps            : 31
% 0.13/0.42  # Proof object formula steps           : 21
% 0.13/0.42  # Proof object conjectures             : 14
% 0.13/0.42  # Proof object clause conjectures      : 11
% 0.13/0.42  # Proof object formula conjectures     : 3
% 0.13/0.42  # Proof object initial clauses used    : 13
% 0.13/0.42  # Proof object initial formulas used   : 10
% 0.13/0.42  # Proof object generating inferences   : 12
% 0.13/0.42  # Proof object simplifying inferences  : 13
% 0.13/0.42  # Training examples: 0 positive, 0 negative
% 0.13/0.42  # Parsed axioms                        : 10
% 0.13/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.42  # Initial clauses                      : 21
% 0.13/0.42  # Removed in clause preprocessing      : 1
% 0.13/0.42  # Initial clauses in saturation        : 20
% 0.13/0.42  # Processed clauses                    : 352
% 0.13/0.42  # ...of these trivial                  : 19
% 0.13/0.42  # ...subsumed                          : 197
% 0.13/0.42  # ...remaining for further processing  : 136
% 0.13/0.42  # Other redundant clauses eliminated   : 67
% 0.13/0.42  # Clauses deleted for lack of memory   : 0
% 0.13/0.42  # Backward-subsumed                    : 0
% 0.13/0.42  # Backward-rewritten                   : 25
% 0.13/0.42  # Generated clauses                    : 3114
% 0.13/0.42  # ...of the previous two non-trivial   : 2806
% 0.13/0.42  # Contextual simplify-reflections      : 5
% 0.13/0.42  # Paramodulations                      : 3047
% 0.13/0.42  # Factorizations                       : 0
% 0.13/0.42  # Equation resolutions                 : 67
% 0.13/0.42  # Propositional unsat checks           : 0
% 0.13/0.42  #    Propositional check models        : 0
% 0.13/0.42  #    Propositional check unsatisfiable : 0
% 0.13/0.42  #    Propositional clauses             : 0
% 0.13/0.42  #    Propositional clauses after purity: 0
% 0.13/0.42  #    Propositional unsat core size     : 0
% 0.13/0.42  #    Propositional preprocessing time  : 0.000
% 0.13/0.42  #    Propositional encoding time       : 0.000
% 0.13/0.42  #    Propositional solver time         : 0.000
% 0.13/0.42  #    Success case prop preproc time    : 0.000
% 0.13/0.42  #    Success case prop encoding time   : 0.000
% 0.13/0.42  #    Success case prop solver time     : 0.000
% 0.13/0.42  # Current number of processed clauses  : 85
% 0.13/0.42  #    Positive orientable unit clauses  : 24
% 0.13/0.42  #    Positive unorientable unit clauses: 0
% 0.13/0.42  #    Negative unit clauses             : 3
% 0.13/0.42  #    Non-unit-clauses                  : 58
% 0.13/0.42  # Current number of unprocessed clauses: 2476
% 0.13/0.42  # ...number of literals in the above   : 7777
% 0.13/0.42  # Current number of archived formulas  : 0
% 0.13/0.42  # Current number of archived clauses   : 46
% 0.13/0.42  # Clause-clause subsumption calls (NU) : 1450
% 0.13/0.42  # Rec. Clause-clause subsumption calls : 1179
% 0.13/0.42  # Non-unit clause-clause subsumptions  : 175
% 0.13/0.42  # Unit Clause-clause subsumption calls : 98
% 0.13/0.42  # Rewrite failures with RHS unbound    : 0
% 0.13/0.42  # BW rewrite match attempts            : 62
% 0.13/0.42  # BW rewrite match successes           : 5
% 0.13/0.42  # Condensation attempts                : 0
% 0.13/0.42  # Condensation successes               : 0
% 0.13/0.42  # Termbank termtop insertions          : 45239
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.067 s
% 0.20/0.43  # System time              : 0.006 s
% 0.20/0.43  # Total time               : 0.073 s
% 0.20/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
