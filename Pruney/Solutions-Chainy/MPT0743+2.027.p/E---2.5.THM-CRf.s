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
% DateTime   : Thu Dec  3 10:56:19 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 577 expanded)
%              Number of clauses        :   38 ( 246 expanded)
%              Number of leaves         :   11 ( 144 expanded)
%              Depth                    :   13
%              Number of atoms          :  170 (1774 expanded)
%              Number of equality atoms :   18 ( 165 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t33_ordinal1,conjecture,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r2_hidden(X1,X2)
          <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(d1_ordinal1,axiom,(
    ! [X1] : k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(t13_ordinal1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,k1_ordinal1(X2))
    <=> ( r2_hidden(X1,X2)
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(redefinition_r1_ordinal1,axiom,(
    ! [X1,X2] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X2) )
     => ( r1_ordinal1(X1,X2)
      <=> r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(t29_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => v3_ordinal1(k1_ordinal1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t26_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ! [X2] :
          ( v3_ordinal1(X2)
         => ( r1_ordinal1(X1,X2)
            | r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d2_ordinal1,axiom,(
    ! [X1] :
      ( v1_ordinal1(X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(cc1_ordinal1,axiom,(
    ! [X1] :
      ( v3_ordinal1(X1)
     => ( v1_ordinal1(X1)
        & v2_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(t10_ordinal1,axiom,(
    ! [X1] : r2_hidden(X1,k1_ordinal1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( v3_ordinal1(X1)
       => ! [X2] :
            ( v3_ordinal1(X2)
           => ( r2_hidden(X1,X2)
            <=> r1_ordinal1(k1_ordinal1(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t33_ordinal1])).

fof(c_0_12,negated_conjecture,
    ( v3_ordinal1(esk2_0)
    & v3_ordinal1(esk3_0)
    & ( ~ r2_hidden(esk2_0,esk3_0)
      | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) )
    & ( r2_hidden(esk2_0,esk3_0)
      | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_13,plain,(
    ! [X6] : k1_ordinal1(X6) = k2_xboole_0(X6,k1_tarski(X6)) ),
    inference(variable_rename,[status(thm)],[d1_ordinal1])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ( ~ r2_hidden(X14,k1_ordinal1(X15))
        | r2_hidden(X14,X15)
        | X14 = X15 )
      & ( ~ r2_hidden(X14,X15)
        | r2_hidden(X14,k1_ordinal1(X15)) )
      & ( X14 != X15
        | r2_hidden(X14,k1_ordinal1(X15)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).

fof(c_0_15,plain,(
    ! [X11,X12] :
      ( ( ~ r1_ordinal1(X11,X12)
        | r1_tarski(X11,X12)
        | ~ v3_ordinal1(X11)
        | ~ v3_ordinal1(X12) )
      & ( ~ r1_tarski(X11,X12)
        | r1_ordinal1(X11,X12)
        | ~ v3_ordinal1(X11)
        | ~ v3_ordinal1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_ordinal1(X1) = k2_xboole_0(X1,k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18] :
      ( ~ v3_ordinal1(X18)
      | v3_ordinal1(k1_ordinal1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).

fof(c_0_19,plain,(
    ! [X19,X20] :
      ( ~ r2_hidden(X19,X20)
      | ~ r1_tarski(X20,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,k1_ordinal1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_ordinal1(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v3_ordinal1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( v3_ordinal1(k1_ordinal1(X1))
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X16,X17] :
      ( ~ v3_ordinal1(X16)
      | ~ v3_ordinal1(X17)
      | r1_ordinal1(X16,X17)
      | r2_hidden(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_20,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_29,plain,
    ( v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1) ),
    inference(rw,[status(thm)],[c_0_24,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( v3_ordinal1(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k1_ordinal1(esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_32,plain,(
    ! [X3,X4] :
      ( ( r1_tarski(X3,X4)
        | X3 != X4 )
      & ( r1_tarski(X4,X3)
        | X3 != X4 )
      & ( ~ r1_tarski(X3,X4)
        | ~ r1_tarski(X4,X3)
        | X3 = X4 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_33,plain,
    ( r1_ordinal1(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

fof(c_0_36,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_ordinal1(X7)
        | ~ r2_hidden(X8,X7)
        | r1_tarski(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_ordinal1(X9) )
      & ( ~ r1_tarski(esk1_1(X9),X9)
        | v1_ordinal1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).

fof(c_0_37,plain,(
    ! [X5] :
      ( ( v1_ordinal1(X5)
        | ~ v3_ordinal1(X5) )
      & ( v2_ordinal1(X5)
        | ~ v3_ordinal1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | X1 = X2
    | ~ r2_hidden(X1,k1_ordinal1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk3_0)
    | ~ r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | r1_tarski(X2,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_0,esk3_0)
    | ~ r2_hidden(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(X2,X1)
    | ~ v1_ordinal1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,plain,
    ( v1_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2))) ),
    inference(rw,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))
    | ~ r2_hidden(esk2_0,esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_33]),c_0_23])])).

cnf(c_0_47,plain,
    ( X1 = X2
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0)
    | ~ r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,X2)
    | ~ v3_ordinal1(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_50,plain,(
    ! [X13] : r2_hidden(X13,k1_ordinal1(X13)) ),
    inference(variable_rename,[status(thm)],[t10_ordinal1])).

cnf(c_0_51,negated_conjecture,
    ( esk2_0 = esk3_0
    | r2_hidden(esk3_0,esk2_0)
    | ~ r2_hidden(esk2_0,esk3_0)
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( X1 = X2
    | r2_hidden(X1,X2)
    | r2_hidden(X2,X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_30])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,k1_ordinal1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( esk2_0 = esk3_0
    | ~ v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_30]),c_0_23])]),c_0_53])).

cnf(c_0_56,plain,
    ( r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(rw,[status(thm)],[c_0_54,c_0_17])).

cnf(c_0_57,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_29]),c_0_30])])).

cnf(c_0_58,plain,
    ( ~ r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_57]),c_0_57]),c_0_57]),c_0_58]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:39:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___107_C41_F1_PI_AE_Q4_CS_SP_PS_S2U
% 0.14/0.40  # and selection function SelectNewComplexAHPExceptRRHorn.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.048 s
% 0.14/0.40  # Presaturation interreduction done
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t33_ordinal1, conjecture, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 0.14/0.40  fof(d1_ordinal1, axiom, ![X1]:k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 0.14/0.40  fof(t13_ordinal1, axiom, ![X1, X2]:(r2_hidden(X1,k1_ordinal1(X2))<=>(r2_hidden(X1,X2)|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 0.14/0.40  fof(redefinition_r1_ordinal1, axiom, ![X1, X2]:((v3_ordinal1(X1)&v3_ordinal1(X2))=>(r1_ordinal1(X1,X2)<=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 0.14/0.40  fof(t29_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>v3_ordinal1(k1_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 0.14/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.40  fof(t26_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r1_ordinal1(X1,X2)|r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 0.14/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.40  fof(d2_ordinal1, axiom, ![X1]:(v1_ordinal1(X1)<=>![X2]:(r2_hidden(X2,X1)=>r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 0.14/0.40  fof(cc1_ordinal1, axiom, ![X1]:(v3_ordinal1(X1)=>(v1_ordinal1(X1)&v2_ordinal1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 0.14/0.40  fof(t10_ordinal1, axiom, ![X1]:r2_hidden(X1,k1_ordinal1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 0.14/0.40  fof(c_0_11, negated_conjecture, ~(![X1]:(v3_ordinal1(X1)=>![X2]:(v3_ordinal1(X2)=>(r2_hidden(X1,X2)<=>r1_ordinal1(k1_ordinal1(X1),X2))))), inference(assume_negation,[status(cth)],[t33_ordinal1])).
% 0.14/0.40  fof(c_0_12, negated_conjecture, (v3_ordinal1(esk2_0)&(v3_ordinal1(esk3_0)&((~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))&(r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).
% 0.14/0.40  fof(c_0_13, plain, ![X6]:k1_ordinal1(X6)=k2_xboole_0(X6,k1_tarski(X6)), inference(variable_rename,[status(thm)],[d1_ordinal1])).
% 0.14/0.40  fof(c_0_14, plain, ![X14, X15]:((~r2_hidden(X14,k1_ordinal1(X15))|(r2_hidden(X14,X15)|X14=X15))&((~r2_hidden(X14,X15)|r2_hidden(X14,k1_ordinal1(X15)))&(X14!=X15|r2_hidden(X14,k1_ordinal1(X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_ordinal1])])])).
% 0.14/0.40  fof(c_0_15, plain, ![X11, X12]:((~r1_ordinal1(X11,X12)|r1_tarski(X11,X12)|(~v3_ordinal1(X11)|~v3_ordinal1(X12)))&(~r1_tarski(X11,X12)|r1_ordinal1(X11,X12)|(~v3_ordinal1(X11)|~v3_ordinal1(X12)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r1_ordinal1])])])).
% 0.14/0.40  cnf(c_0_16, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_17, plain, (k1_ordinal1(X1)=k2_xboole_0(X1,k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.40  fof(c_0_18, plain, ![X18]:(~v3_ordinal1(X18)|v3_ordinal1(k1_ordinal1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_ordinal1])])).
% 0.14/0.40  fof(c_0_19, plain, ![X19, X20]:(~r2_hidden(X19,X20)|~r1_tarski(X20,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.40  cnf(c_0_20, plain, (r2_hidden(X1,k1_ordinal1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r1_ordinal1(X1,X2)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.14/0.40  cnf(c_0_23, negated_conjecture, (v3_ordinal1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_24, plain, (v3_ordinal1(k1_ordinal1(X1))|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.40  fof(c_0_25, plain, ![X16, X17]:(~v3_ordinal1(X16)|(~v3_ordinal1(X17)|(r1_ordinal1(X16,X17)|r2_hidden(X17,X16)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_ordinal1])])])).
% 0.14/0.40  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.40  cnf(c_0_27, plain, (r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_20, c_0_17])).
% 0.14/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.14/0.40  cnf(c_0_29, plain, (v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))|~v3_ordinal1(X1)), inference(rw,[status(thm)],[c_0_24, c_0_17])).
% 0.14/0.40  cnf(c_0_30, negated_conjecture, (v3_ordinal1(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k1_ordinal1(esk2_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.40  fof(c_0_32, plain, ![X3, X4]:(((r1_tarski(X3,X4)|X3!=X4)&(r1_tarski(X4,X3)|X3!=X4))&(~r1_tarski(X3,X4)|~r1_tarski(X4,X3)|X3=X4)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.40  cnf(c_0_33, plain, (r1_ordinal1(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.40  cnf(c_0_34, plain, (~r2_hidden(X1,X2)|~r1_tarski(k2_xboole_0(X2,k1_tarski(X2)),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.40  cnf(c_0_35, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|r1_tarski(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.14/0.40  fof(c_0_36, plain, ![X7, X8, X9]:((~v1_ordinal1(X7)|(~r2_hidden(X8,X7)|r1_tarski(X8,X7)))&((r2_hidden(esk1_1(X9),X9)|v1_ordinal1(X9))&(~r1_tarski(esk1_1(X9),X9)|v1_ordinal1(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_ordinal1])])])])])])).
% 0.14/0.40  fof(c_0_37, plain, ![X5]:((v1_ordinal1(X5)|~v3_ordinal1(X5))&(v2_ordinal1(X5)|~v3_ordinal1(X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_ordinal1])])])).
% 0.14/0.40  cnf(c_0_38, plain, (r2_hidden(X1,X2)|X1=X2|~r2_hidden(X1,k1_ordinal1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.40  cnf(c_0_39, negated_conjecture, (~r2_hidden(esk2_0,esk3_0)|~r1_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)),esk3_0)), inference(rw,[status(thm)],[c_0_31, c_0_17])).
% 0.14/0.40  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.40  cnf(c_0_41, plain, (r2_hidden(X1,X2)|r1_tarski(X2,X1)|~v3_ordinal1(X1)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_21, c_0_33])).
% 0.14/0.40  cnf(c_0_42, negated_conjecture, (r2_hidden(esk2_0,esk3_0)|~r2_hidden(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.40  cnf(c_0_43, plain, (r1_tarski(X2,X1)|~v1_ordinal1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_44, plain, (v1_ordinal1(X1)|~v3_ordinal1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.40  cnf(c_0_45, plain, (X1=X2|r2_hidden(X1,X2)|~r2_hidden(X1,k2_xboole_0(X2,k1_tarski(X2)))), inference(rw,[status(thm)],[c_0_38, c_0_17])).
% 0.14/0.40  cnf(c_0_46, negated_conjecture, (r2_hidden(esk3_0,k2_xboole_0(esk2_0,k1_tarski(esk2_0)))|~r2_hidden(esk2_0,esk3_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_33]), c_0_23])])).
% 0.14/0.40  cnf(c_0_47, plain, (X1=X2|r2_hidden(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.14/0.40  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)|~r1_tarski(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_42])).
% 0.14/0.40  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,X2)|~v3_ordinal1(X2)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.14/0.40  fof(c_0_50, plain, ![X13]:r2_hidden(X13,k1_ordinal1(X13)), inference(variable_rename,[status(thm)],[t10_ordinal1])).
% 0.14/0.40  cnf(c_0_51, negated_conjecture, (esk2_0=esk3_0|r2_hidden(esk3_0,esk2_0)|~r2_hidden(esk2_0,esk3_0)|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.40  cnf(c_0_52, plain, (X1=X2|r2_hidden(X1,X2)|r2_hidden(X2,X1)|~v3_ordinal1(X2)|~v3_ordinal1(X1)), inference(spm,[status(thm)],[c_0_47, c_0_41])).
% 0.14/0.40  cnf(c_0_53, negated_conjecture, (~r2_hidden(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_30])])).
% 0.14/0.40  cnf(c_0_54, plain, (r2_hidden(X1,k1_ordinal1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.40  cnf(c_0_55, negated_conjecture, (esk2_0=esk3_0|~v3_ordinal1(k2_xboole_0(esk2_0,k1_tarski(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_30]), c_0_23])]), c_0_53])).
% 0.14/0.40  cnf(c_0_56, plain, (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))), inference(rw,[status(thm)],[c_0_54, c_0_17])).
% 0.14/0.40  cnf(c_0_57, negated_conjecture, (esk2_0=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_29]), c_0_30])])).
% 0.14/0.40  cnf(c_0_58, plain, (~r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),X1)), inference(spm,[status(thm)],[c_0_26, c_0_56])).
% 0.14/0.40  cnf(c_0_59, negated_conjecture, (~r2_hidden(esk3_0,esk3_0)), inference(rw,[status(thm)],[c_0_53, c_0_57])).
% 0.14/0.40  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_57]), c_0_57]), c_0_57]), c_0_58]), c_0_59]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 61
% 0.14/0.40  # Proof object clause steps            : 38
% 0.14/0.40  # Proof object formula steps           : 23
% 0.14/0.40  # Proof object conjectures             : 20
% 0.14/0.40  # Proof object clause conjectures      : 17
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 15
% 0.14/0.40  # Proof object initial formulas used   : 11
% 0.14/0.40  # Proof object generating inferences   : 15
% 0.14/0.40  # Proof object simplifying inferences  : 26
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 11
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 22
% 0.14/0.40  # Removed in clause preprocessing      : 1
% 0.14/0.40  # Initial clauses in saturation        : 21
% 0.14/0.40  # Processed clauses                    : 102
% 0.14/0.40  # ...of these trivial                  : 1
% 0.14/0.40  # ...subsumed                          : 23
% 0.14/0.40  # ...remaining for further processing  : 77
% 0.14/0.40  # Other redundant clauses eliminated   : 3
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 4
% 0.14/0.40  # Backward-rewritten                   : 15
% 0.14/0.40  # Generated clauses                    : 114
% 0.14/0.40  # ...of the previous two non-trivial   : 105
% 0.14/0.40  # Contextual simplify-reflections      : 0
% 0.14/0.40  # Paramodulations                      : 108
% 0.14/0.40  # Factorizations                       : 2
% 0.14/0.40  # Equation resolutions                 : 3
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 35
% 0.14/0.40  #    Positive orientable unit clauses  : 4
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 4
% 0.14/0.40  #    Non-unit-clauses                  : 27
% 0.14/0.40  # Current number of unprocessed clauses: 43
% 0.14/0.40  # ...number of literals in the above   : 154
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 40
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 255
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 189
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 21
% 0.14/0.40  # Unit Clause-clause subsumption calls : 13
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 4
% 0.14/0.40  # BW rewrite match successes           : 1
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 2868
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.055 s
% 0.14/0.40  # System time              : 0.004 s
% 0.14/0.40  # Total time               : 0.059 s
% 0.14/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
