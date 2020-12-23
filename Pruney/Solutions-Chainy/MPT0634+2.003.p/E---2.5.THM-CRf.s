%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:19 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 435 expanded)
%              Number of clauses        :   33 ( 175 expanded)
%              Number of leaves         :   10 ( 121 expanded)
%              Depth                    :    9
%              Number of atoms          :  184 (1027 expanded)
%              Number of equality atoms :   54 ( 408 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t37_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_1)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t34_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( X2 = k6_relat_1(X1)
      <=> ( k1_relat_1(X2) = X1
          & ! [X3] :
              ( r2_hidden(X3,X1)
             => k1_funct_1(X2,X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(t21_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_relat_1(X3)
            & v1_funct_1(X3) )
         => ( r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))
          <=> ( r2_hidden(X1,k1_relat_1(X3))
              & r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(k1_relat_1(X2),X1) ) ),
    inference(assume_negation,[status(cth)],[t37_funct_1])).

fof(c_0_11,plain,(
    ! [X21,X22] : k1_setfam_1(k2_tarski(X21,X22)) = k3_xboole_0(X21,X22) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_12,plain,(
    ! [X16,X17] : k1_enumset1(X16,X16,X17) = k2_tarski(X16,X17) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk4_0)
    & v1_funct_1(esk4_0)
    & k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)) != k3_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_14,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] : k2_enumset1(X18,X18,X19,X20) = k1_enumset1(X18,X19,X20) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_17,plain,(
    ! [X14,X15] : k2_tarski(X14,X15) = k2_tarski(X15,X14) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_18,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)) != k3_xboole_0(k1_relat_1(esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
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

fof(c_0_23,plain,(
    ! [X28,X29,X30] :
      ( ( k1_relat_1(X29) = X28
        | X29 != k6_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X30,X28)
        | k1_funct_1(X29,X30) = X30
        | X29 != k6_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk2_2(X28,X29),X28)
        | k1_relat_1(X29) != X28
        | X29 = k6_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( k1_funct_1(X29,esk2_2(X28,X29)) != esk2_2(X28,X29)
        | k1_relat_1(X29) != X28
        | X29 = k6_relat_1(X28)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).

fof(c_0_24,plain,(
    ! [X24] :
      ( v1_relat_1(k6_relat_1(X24))
      & v1_funct_1(k6_relat_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

cnf(c_0_25,negated_conjecture,
    ( k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)) != k1_setfam_1(k2_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18,c_0_19]),c_0_20])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X1,X2) = k2_enumset1(X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21,c_0_15]),c_0_15]),c_0_20]),c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X25,X26,X27] :
      ( ( r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))
        | ~ r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) )
      & ( ~ r2_hidden(X25,k1_relat_1(X27))
        | ~ r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))
        | r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))
        | ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).

cnf(c_0_29,plain,
    ( k1_funct_1(X3,X1) = X1
    | ~ r2_hidden(X1,X2)
    | X3 != k6_relat_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_30,plain,
    ( v1_funct_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_32,plain,(
    ! [X23] :
      ( k1_relat_1(k6_relat_1(X23)) = X23
      & k2_relat_1(k6_relat_1(X23)) = X23 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_33,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X2)
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_34,negated_conjecture,
    ( k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,k1_relat_1(esk4_0))) != k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_19]),c_0_20])).

cnf(c_0_36,plain,
    ( X3 = k3_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k1_funct_1(k6_relat_1(X1),X2) = X2
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_39,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))
    | ~ r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | r2_hidden(esk1_3(X1,X2,X3),X3)
    | r2_hidden(esk1_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_19]),c_0_20])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)))
    | r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),esk3_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_46,plain,
    ( X3 = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_19]),c_0_20])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)))
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_relat_1(X3))
    | ~ r2_hidden(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30]),c_0_31]),c_0_39])])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),X2)))
    | ~ r2_hidden(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_30]),c_0_31])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)))
    | r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(esk4_0)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_41])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_39]),c_0_44]),c_0_30]),c_0_45]),c_0_31])])).

cnf(c_0_51,plain,
    ( k1_relat_1(k5_relat_1(k6_relat_1(X1),X2)) = k1_setfam_1(k2_enumset1(X3,X3,X3,X4))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),k1_relat_1(X2))
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X4)
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X3)
    | ~ r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_44]),c_0_45]),c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_44]),c_0_45]),c_0_52]),c_0_50])]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 2.13/2.35  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.13/2.35  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.13/2.35  #
% 2.13/2.35  # Preprocessing time       : 0.028 s
% 2.13/2.35  # Presaturation interreduction done
% 2.13/2.35  
% 2.13/2.35  # Proof found!
% 2.13/2.35  # SZS status Theorem
% 2.13/2.35  # SZS output start CNFRefutation
% 2.13/2.35  fof(t37_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_funct_1)).
% 2.13/2.35  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.13/2.35  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.13/2.35  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.13/2.35  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.13/2.35  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.13/2.35  fof(t34_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(X2=k6_relat_1(X1)<=>(k1_relat_1(X2)=X1&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.13/2.35  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.13/2.35  fof(t21_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,k1_relat_1(k5_relat_1(X3,X2)))<=>(r2_hidden(X1,k1_relat_1(X3))&r2_hidden(k1_funct_1(X3,X1),k1_relat_1(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 2.13/2.35  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.13/2.35  fof(c_0_10, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k3_xboole_0(k1_relat_1(X2),X1))), inference(assume_negation,[status(cth)],[t37_funct_1])).
% 2.13/2.35  fof(c_0_11, plain, ![X21, X22]:k1_setfam_1(k2_tarski(X21,X22))=k3_xboole_0(X21,X22), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 2.13/2.35  fof(c_0_12, plain, ![X16, X17]:k1_enumset1(X16,X16,X17)=k2_tarski(X16,X17), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 2.13/2.35  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk4_0)&v1_funct_1(esk4_0))&k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))!=k3_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 2.13/2.35  cnf(c_0_14, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 2.13/2.35  cnf(c_0_15, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 2.13/2.35  fof(c_0_16, plain, ![X18, X19, X20]:k2_enumset1(X18,X18,X19,X20)=k1_enumset1(X18,X19,X20), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 2.13/2.35  fof(c_0_17, plain, ![X14, X15]:k2_tarski(X14,X15)=k2_tarski(X15,X14), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 2.13/2.35  cnf(c_0_18, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))!=k3_xboole_0(k1_relat_1(esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.13/2.35  cnf(c_0_19, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 2.13/2.35  cnf(c_0_20, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 2.13/2.35  cnf(c_0_21, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 2.13/2.35  fof(c_0_22, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:((((r2_hidden(X8,X5)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6))&(r2_hidden(X8,X6)|~r2_hidden(X8,X7)|X7!=k3_xboole_0(X5,X6)))&(~r2_hidden(X9,X5)|~r2_hidden(X9,X6)|r2_hidden(X9,X7)|X7!=k3_xboole_0(X5,X6)))&((~r2_hidden(esk1_3(X10,X11,X12),X12)|(~r2_hidden(esk1_3(X10,X11,X12),X10)|~r2_hidden(esk1_3(X10,X11,X12),X11))|X12=k3_xboole_0(X10,X11))&((r2_hidden(esk1_3(X10,X11,X12),X10)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))&(r2_hidden(esk1_3(X10,X11,X12),X11)|r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k3_xboole_0(X10,X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 2.13/2.35  fof(c_0_23, plain, ![X28, X29, X30]:(((k1_relat_1(X29)=X28|X29!=k6_relat_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(~r2_hidden(X30,X28)|k1_funct_1(X29,X30)=X30|X29!=k6_relat_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((r2_hidden(esk2_2(X28,X29),X28)|k1_relat_1(X29)!=X28|X29=k6_relat_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(k1_funct_1(X29,esk2_2(X28,X29))!=esk2_2(X28,X29)|k1_relat_1(X29)!=X28|X29=k6_relat_1(X28)|(~v1_relat_1(X29)|~v1_funct_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_funct_1])])])])])).
% 2.13/2.35  fof(c_0_24, plain, ![X24]:(v1_relat_1(k6_relat_1(X24))&v1_funct_1(k6_relat_1(X24))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 2.13/2.35  cnf(c_0_25, negated_conjecture, (k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))!=k1_setfam_1(k2_enumset1(k1_relat_1(esk4_0),k1_relat_1(esk4_0),k1_relat_1(esk4_0),esk3_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 2.13/2.35  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X1,X2)=k2_enumset1(X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_21, c_0_15]), c_0_15]), c_0_20]), c_0_20])).
% 2.13/2.35  cnf(c_0_27, plain, (r2_hidden(esk1_3(X1,X2,X3),X1)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.13/2.35  fof(c_0_28, plain, ![X25, X26, X27]:(((r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))&(r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))|~r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26))))&(~r2_hidden(X25,k1_relat_1(X27))|~r2_hidden(k1_funct_1(X27,X25),k1_relat_1(X26))|r2_hidden(X25,k1_relat_1(k5_relat_1(X27,X26)))|(~v1_relat_1(X27)|~v1_funct_1(X27))|(~v1_relat_1(X26)|~v1_funct_1(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_funct_1])])])])).
% 2.13/2.35  cnf(c_0_29, plain, (k1_funct_1(X3,X1)=X1|~r2_hidden(X1,X2)|X3!=k6_relat_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.13/2.35  cnf(c_0_30, plain, (v1_funct_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.13/2.35  cnf(c_0_31, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 2.13/2.35  fof(c_0_32, plain, ![X23]:(k1_relat_1(k6_relat_1(X23))=X23&k2_relat_1(k6_relat_1(X23))=X23), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 2.13/2.35  cnf(c_0_33, plain, (r2_hidden(esk1_3(X1,X2,X3),X2)|r2_hidden(esk1_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.13/2.35  cnf(c_0_34, negated_conjecture, (k1_setfam_1(k2_enumset1(esk3_0,esk3_0,esk3_0,k1_relat_1(esk4_0)))!=k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 2.13/2.35  cnf(c_0_35, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27, c_0_19]), c_0_20])).
% 2.13/2.35  cnf(c_0_36, plain, (X3=k3_xboole_0(X1,X2)|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X1)|~r2_hidden(esk1_3(X1,X2,X3),X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.13/2.35  cnf(c_0_37, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k1_funct_1(X2,X1),k1_relat_1(X3))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.13/2.35  cnf(c_0_38, plain, (k1_funct_1(k6_relat_1(X1),X2)=X2|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_29]), c_0_30]), c_0_31])])).
% 2.13/2.35  cnf(c_0_39, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.13/2.35  cnf(c_0_40, plain, (r2_hidden(k1_funct_1(X1,X2),k1_relat_1(X3))|~r2_hidden(X2,k1_relat_1(k5_relat_1(X1,X3)))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.13/2.35  cnf(c_0_41, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|r2_hidden(esk1_3(X1,X2,X3),X3)|r2_hidden(esk1_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_19]), c_0_20])).
% 2.13/2.35  cnf(c_0_42, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(X1,k1_relat_1(k5_relat_1(X2,X3)))|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X3)|~v1_funct_1(X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 2.13/2.35  cnf(c_0_43, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)))|r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),esk3_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35])])).
% 2.13/2.35  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.13/2.35  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 2.13/2.35  cnf(c_0_46, plain, (X3=k1_setfam_1(k2_enumset1(X1,X1,X1,X2))|~r2_hidden(esk1_3(X1,X2,X3),X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~r2_hidden(esk1_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_19]), c_0_20])).
% 2.13/2.35  cnf(c_0_47, plain, (r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X2),X3)))|~v1_funct_1(X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_relat_1(X3))|~r2_hidden(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_30]), c_0_31]), c_0_39])])).
% 2.13/2.35  cnf(c_0_48, plain, (r2_hidden(X1,k1_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(k5_relat_1(k6_relat_1(X3),X2)))|~r2_hidden(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_38]), c_0_30]), c_0_31])])).
% 2.13/2.35  cnf(c_0_49, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0)))|r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(esk4_0))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_41])])).
% 2.13/2.35  cnf(c_0_50, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_39]), c_0_44]), c_0_30]), c_0_45]), c_0_31])])).
% 2.13/2.35  cnf(c_0_51, plain, (k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))=k1_setfam_1(k2_enumset1(X3,X3,X3,X4))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),k1_relat_1(X2))|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X4)|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X3)|~r2_hidden(esk1_3(X3,X4,k1_relat_1(k5_relat_1(k6_relat_1(X1),X2))),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.13/2.35  cnf(c_0_52, negated_conjecture, (r2_hidden(esk1_3(esk3_0,k1_relat_1(esk4_0),k1_relat_1(k5_relat_1(k6_relat_1(esk3_0),esk4_0))),k1_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_44]), c_0_45]), c_0_50])])).
% 2.13/2.35  cnf(c_0_53, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_44]), c_0_45]), c_0_52]), c_0_50])]), c_0_34]), ['proof']).
% 2.13/2.35  # SZS output end CNFRefutation
% 2.13/2.35  # Proof object total steps             : 54
% 2.13/2.35  # Proof object clause steps            : 33
% 2.13/2.35  # Proof object formula steps           : 21
% 2.13/2.35  # Proof object conjectures             : 13
% 2.13/2.35  # Proof object clause conjectures      : 10
% 2.13/2.35  # Proof object formula conjectures     : 3
% 2.13/2.35  # Proof object initial clauses used    : 17
% 2.13/2.35  # Proof object initial formulas used   : 10
% 2.13/2.35  # Proof object generating inferences   : 8
% 2.13/2.35  # Proof object simplifying inferences  : 43
% 2.13/2.35  # Training examples: 0 positive, 0 negative
% 2.13/2.35  # Parsed axioms                        : 10
% 2.13/2.35  # Removed by relevancy pruning/SinE    : 0
% 2.13/2.35  # Initial clauses                      : 24
% 2.13/2.35  # Removed in clause preprocessing      : 3
% 2.13/2.35  # Initial clauses in saturation        : 21
% 2.13/2.35  # Processed clauses                    : 2657
% 2.13/2.35  # ...of these trivial                  : 30
% 2.13/2.35  # ...subsumed                          : 1231
% 2.13/2.35  # ...remaining for further processing  : 1396
% 2.13/2.35  # Other redundant clauses eliminated   : 794
% 2.13/2.35  # Clauses deleted for lack of memory   : 0
% 2.13/2.35  # Backward-subsumed                    : 84
% 2.13/2.35  # Backward-rewritten                   : 88
% 2.13/2.35  # Generated clauses                    : 140371
% 2.13/2.35  # ...of the previous two non-trivial   : 134594
% 2.13/2.35  # Contextual simplify-reflections      : 36
% 2.13/2.35  # Paramodulations                      : 139383
% 2.13/2.35  # Factorizations                       : 194
% 2.13/2.35  # Equation resolutions                 : 794
% 2.13/2.35  # Propositional unsat checks           : 0
% 2.13/2.35  #    Propositional check models        : 0
% 2.13/2.35  #    Propositional check unsatisfiable : 0
% 2.13/2.35  #    Propositional clauses             : 0
% 2.13/2.35  #    Propositional clauses after purity: 0
% 2.13/2.35  #    Propositional unsat core size     : 0
% 2.13/2.35  #    Propositional preprocessing time  : 0.000
% 2.13/2.35  #    Propositional encoding time       : 0.000
% 2.13/2.35  #    Propositional solver time         : 0.000
% 2.13/2.35  #    Success case prop preproc time    : 0.000
% 2.13/2.35  #    Success case prop encoding time   : 0.000
% 2.13/2.35  #    Success case prop solver time     : 0.000
% 2.13/2.35  # Current number of processed clauses  : 1197
% 2.13/2.35  #    Positive orientable unit clauses  : 26
% 2.13/2.35  #    Positive unorientable unit clauses: 1
% 2.13/2.35  #    Negative unit clauses             : 1
% 2.13/2.35  #    Non-unit-clauses                  : 1169
% 2.13/2.35  # Current number of unprocessed clauses: 131511
% 2.13/2.35  # ...number of literals in the above   : 841568
% 2.13/2.35  # Current number of archived formulas  : 0
% 2.13/2.35  # Current number of archived clauses   : 195
% 2.13/2.35  # Clause-clause subsumption calls (NU) : 277673
% 2.13/2.35  # Rec. Clause-clause subsumption calls : 122197
% 2.13/2.35  # Non-unit clause-clause subsumptions  : 1336
% 2.13/2.35  # Unit Clause-clause subsumption calls : 2595
% 2.13/2.35  # Rewrite failures with RHS unbound    : 0
% 2.13/2.35  # BW rewrite match attempts            : 324
% 2.13/2.35  # BW rewrite match successes           : 24
% 2.13/2.35  # Condensation attempts                : 0
% 2.13/2.35  # Condensation successes               : 0
% 2.13/2.35  # Termbank termtop insertions          : 4945637
% 2.13/2.35  
% 2.13/2.35  # -------------------------------------------------
% 2.13/2.35  # User time                : 1.944 s
% 2.13/2.35  # System time              : 0.071 s
% 2.13/2.35  # Total time               : 2.016 s
% 2.13/2.35  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
