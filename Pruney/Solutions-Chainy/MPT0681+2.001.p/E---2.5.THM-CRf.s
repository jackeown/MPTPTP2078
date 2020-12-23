%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:26 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 105 expanded)
%              Number of clauses        :   23 (  45 expanded)
%              Number of leaves         :    6 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  138 ( 313 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t125_funct_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r1_xboole_0(X1,X2)
          & v2_funct_1(X3) )
       => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(t121_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( v2_funct_1(X3)
       => k9_relat_1(X3,k3_xboole_0(X1,X2)) = k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

fof(c_0_6,plain,(
    ! [X14,X15] : k1_setfam_1(k2_tarski(X14,X15)) = k3_xboole_0(X14,X15) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_7,plain,(
    ! [X12,X13] : k1_enumset1(X12,X12,X13) = k2_tarski(X12,X13) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_relat_1(X3)
          & v1_funct_1(X3) )
       => ( ( r1_xboole_0(X1,X2)
            & v2_funct_1(X3) )
         => r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t125_funct_1])).

fof(c_0_9,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_12,plain,(
    ! [X16,X17,X18,X19,X21,X22,X23,X24,X26] :
      ( ( r2_hidden(esk2_4(X16,X17,X18,X19),k1_relat_1(X16))
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk2_4(X16,X17,X18,X19),X17)
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( X19 = k1_funct_1(X16,esk2_4(X16,X17,X18,X19))
        | ~ r2_hidden(X19,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(X22,k1_relat_1(X16))
        | ~ r2_hidden(X22,X17)
        | X21 != k1_funct_1(X16,X22)
        | r2_hidden(X21,X18)
        | X18 != k9_relat_1(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( ~ r2_hidden(esk3_3(X16,X23,X24),X24)
        | ~ r2_hidden(X26,k1_relat_1(X16))
        | ~ r2_hidden(X26,X23)
        | esk3_3(X16,X23,X24) != k1_funct_1(X16,X26)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk4_3(X16,X23,X24),k1_relat_1(X16))
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( r2_hidden(esk4_3(X16,X23,X24),X23)
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) )
      & ( esk3_3(X16,X23,X24) = k1_funct_1(X16,esk4_3(X16,X23,X24))
        | r2_hidden(esk3_3(X16,X23,X24),X24)
        | X24 = k9_relat_1(X16,X23)
        | ~ v1_relat_1(X16)
        | ~ v1_funct_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & r1_xboole_0(esk5_0,esk6_0)
    & v2_funct_1(esk7_0)
    & ~ r1_xboole_0(k9_relat_1(esk7_0,esk5_0),k9_relat_1(esk7_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,X2)
    | r2_hidden(esk3_3(esk7_0,X2,X1),X1)
    | r2_hidden(esk4_3(esk7_0,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

fof(c_0_21,plain,(
    ! [X28,X29,X30] :
      ( ~ v1_relat_1(X30)
      | ~ v1_funct_1(X30)
      | ~ v2_funct_1(X30)
      | k9_relat_1(X30,k3_xboole_0(X28,X29)) = k3_xboole_0(k9_relat_1(X30,X28),k9_relat_1(X30,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).

cnf(c_0_22,negated_conjecture,
    ( X1 = k9_relat_1(esk7_0,k1_setfam_1(k1_enumset1(X2,X2,X3)))
    | r2_hidden(esk3_3(esk7_0,k1_setfam_1(k1_enumset1(X2,X2,X3)),X1),X1)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,plain,
    ( k9_relat_1(X1,k3_xboole_0(X2,X3)) = k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k9_relat_1(esk7_0,k1_setfam_1(k1_enumset1(X3,X3,X4)))
    | ~ r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X3,X4) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,X2)
    | r2_hidden(esk1_2(X1,X2),k1_setfam_1(k1_enumset1(X1,X1,X2))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_15])).

cnf(c_0_27,plain,
    ( k9_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_15]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(X1,k9_relat_1(esk7_0,k1_setfam_1(k1_enumset1(X2,X2,X3))))
    | ~ r1_xboole_0(X4,X5)
    | ~ r1_xboole_0(X2,X3) ),
    inference(spm,[status(thm)],[c_0_19,c_0_25])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))))
    | r1_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( v2_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( r1_xboole_0(k9_relat_1(esk7_0,X1),k9_relat_1(esk7_0,X2))
    | ~ r1_xboole_0(X3,X4)
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_17]),c_0_18])])).

cnf(c_0_32,negated_conjecture,
    ( r1_xboole_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(esk7_0,esk5_0),k9_relat_1(esk7_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( r1_xboole_0(k9_relat_1(esk7_0,X1),k9_relat_1(esk7_0,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.21/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.038 s
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.21/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.40  fof(t125_funct_1, conjecture, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 0.21/0.40  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.21/0.40  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.21/0.40  fof(t121_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(v2_funct_1(X3)=>k9_relat_1(X3,k3_xboole_0(X1,X2))=k3_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 0.21/0.40  fof(c_0_6, plain, ![X14, X15]:k1_setfam_1(k2_tarski(X14,X15))=k3_xboole_0(X14,X15), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.21/0.40  fof(c_0_7, plain, ![X12, X13]:k1_enumset1(X12,X12,X13)=k2_tarski(X12,X13), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.40  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r1_xboole_0(X1,X2)&v2_funct_1(X3))=>r1_xboole_0(k9_relat_1(X3,X1),k9_relat_1(X3,X2))))), inference(assume_negation,[status(cth)],[t125_funct_1])).
% 0.21/0.40  fof(c_0_9, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk1_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.21/0.40  cnf(c_0_10, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.40  cnf(c_0_11, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.40  fof(c_0_12, plain, ![X16, X17, X18, X19, X21, X22, X23, X24, X26]:(((((r2_hidden(esk2_4(X16,X17,X18,X19),k1_relat_1(X16))|~r2_hidden(X19,X18)|X18!=k9_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(r2_hidden(esk2_4(X16,X17,X18,X19),X17)|~r2_hidden(X19,X18)|X18!=k9_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(X19=k1_funct_1(X16,esk2_4(X16,X17,X18,X19))|~r2_hidden(X19,X18)|X18!=k9_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(~r2_hidden(X22,k1_relat_1(X16))|~r2_hidden(X22,X17)|X21!=k1_funct_1(X16,X22)|r2_hidden(X21,X18)|X18!=k9_relat_1(X16,X17)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&((~r2_hidden(esk3_3(X16,X23,X24),X24)|(~r2_hidden(X26,k1_relat_1(X16))|~r2_hidden(X26,X23)|esk3_3(X16,X23,X24)!=k1_funct_1(X16,X26))|X24=k9_relat_1(X16,X23)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(((r2_hidden(esk4_3(X16,X23,X24),k1_relat_1(X16))|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k9_relat_1(X16,X23)|(~v1_relat_1(X16)|~v1_funct_1(X16)))&(r2_hidden(esk4_3(X16,X23,X24),X23)|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k9_relat_1(X16,X23)|(~v1_relat_1(X16)|~v1_funct_1(X16))))&(esk3_3(X16,X23,X24)=k1_funct_1(X16,esk4_3(X16,X23,X24))|r2_hidden(esk3_3(X16,X23,X24),X24)|X24=k9_relat_1(X16,X23)|(~v1_relat_1(X16)|~v1_funct_1(X16)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.21/0.40  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&((r1_xboole_0(esk5_0,esk6_0)&v2_funct_1(esk7_0))&~r1_xboole_0(k9_relat_1(esk7_0,esk5_0),k9_relat_1(esk7_0,esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.21/0.40  cnf(c_0_14, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.40  cnf(c_0_15, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.21/0.40  cnf(c_0_16, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.40  cnf(c_0_17, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_18, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_19, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.21/0.40  cnf(c_0_20, negated_conjecture, (X1=k9_relat_1(esk7_0,X2)|r2_hidden(esk3_3(esk7_0,X2,X1),X1)|r2_hidden(esk4_3(esk7_0,X2,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.21/0.40  fof(c_0_21, plain, ![X28, X29, X30]:(~v1_relat_1(X30)|~v1_funct_1(X30)|(~v2_funct_1(X30)|k9_relat_1(X30,k3_xboole_0(X28,X29))=k3_xboole_0(k9_relat_1(X30,X28),k9_relat_1(X30,X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t121_funct_1])])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (X1=k9_relat_1(esk7_0,k1_setfam_1(k1_enumset1(X2,X2,X3)))|r2_hidden(esk3_3(esk7_0,k1_setfam_1(k1_enumset1(X2,X2,X3)),X1),X1)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.40  cnf(c_0_23, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.40  cnf(c_0_24, plain, (k9_relat_1(X1,k3_xboole_0(X2,X3))=k3_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k9_relat_1(esk7_0,k1_setfam_1(k1_enumset1(X3,X3,X4)))|~r1_xboole_0(X1,X2)|~r1_xboole_0(X3,X4)), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.21/0.40  cnf(c_0_26, plain, (r1_xboole_0(X1,X2)|r2_hidden(esk1_2(X1,X2),k1_setfam_1(k1_enumset1(X1,X1,X2)))), inference(rw,[status(thm)],[c_0_23, c_0_15])).
% 0.21/0.40  cnf(c_0_27, plain, (k9_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3)))=k1_setfam_1(k1_enumset1(k9_relat_1(X1,X2),k9_relat_1(X1,X2),k9_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_15]), c_0_15])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (~r2_hidden(X1,k9_relat_1(esk7_0,k1_setfam_1(k1_enumset1(X2,X2,X3))))|~r1_xboole_0(X4,X5)|~r1_xboole_0(X2,X3)), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 0.21/0.40  cnf(c_0_29, plain, (r2_hidden(esk1_2(k9_relat_1(X1,X2),k9_relat_1(X1,X3)),k9_relat_1(X1,k1_setfam_1(k1_enumset1(X2,X2,X3))))|r1_xboole_0(k9_relat_1(X1,X2),k9_relat_1(X1,X3))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.21/0.40  cnf(c_0_30, negated_conjecture, (v2_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_31, negated_conjecture, (r1_xboole_0(k9_relat_1(esk7_0,X1),k9_relat_1(esk7_0,X2))|~r1_xboole_0(X3,X4)|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_17]), c_0_18])])).
% 0.21/0.40  cnf(c_0_32, negated_conjecture, (r1_xboole_0(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_33, negated_conjecture, (~r1_xboole_0(k9_relat_1(esk7_0,esk5_0),k9_relat_1(esk7_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (r1_xboole_0(k9_relat_1(esk7_0,X1),k9_relat_1(esk7_0,X2))|~r1_xboole_0(X1,X2)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_32])]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 36
% 0.21/0.40  # Proof object clause steps            : 23
% 0.21/0.40  # Proof object formula steps           : 13
% 0.21/0.40  # Proof object conjectures             : 15
% 0.21/0.40  # Proof object clause conjectures      : 12
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 11
% 0.21/0.40  # Proof object initial formulas used   : 6
% 0.21/0.40  # Proof object generating inferences   : 8
% 0.21/0.40  # Proof object simplifying inferences  : 13
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 6
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 18
% 0.21/0.40  # Removed in clause preprocessing      : 2
% 0.21/0.40  # Initial clauses in saturation        : 16
% 0.21/0.40  # Processed clauses                    : 104
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 58
% 0.21/0.40  # ...remaining for further processing  : 46
% 0.21/0.40  # Other redundant clauses eliminated   : 5
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 5
% 0.21/0.40  # Backward-rewritten                   : 0
% 0.21/0.40  # Generated clauses                    : 257
% 0.21/0.40  # ...of the previous two non-trivial   : 242
% 0.21/0.40  # Contextual simplify-reflections      : 0
% 0.21/0.40  # Paramodulations                      : 253
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 5
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 37
% 0.21/0.40  #    Positive orientable unit clauses  : 4
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 1
% 0.21/0.40  #    Non-unit-clauses                  : 32
% 0.21/0.40  # Current number of unprocessed clauses: 152
% 0.21/0.40  # ...number of literals in the above   : 756
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 7
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 237
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 102
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 63
% 0.21/0.40  # Unit Clause-clause subsumption calls : 0
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 0
% 0.21/0.40  # BW rewrite match successes           : 0
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 6708
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.053 s
% 0.21/0.40  # System time              : 0.003 s
% 0.21/0.40  # Total time               : 0.056 s
% 0.21/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
