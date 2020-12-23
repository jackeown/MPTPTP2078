%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : zfmisc_1__t143_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 154 expanded)
%              Number of clauses        :   33 (  75 expanded)
%              Number of leaves         :    7 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  100 ( 293 expanded)
%              Number of equality atoms :    6 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',t1_xboole_1)).

fof(t119_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',t119_zfmisc_1)).

fof(t143_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
        & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
     => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',t143_zfmisc_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',t7_xboole_1)).

fof(idempotence_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',idempotence_k2_xboole_0)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t143_zfmisc_1.p',t8_xboole_1)).

fof(c_0_7,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(X24,X25)
      | ~ r1_tarski(X25,X26)
      | r1_tarski(X24,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

fof(c_0_8,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_tarski(X18,X19)
      | r1_tarski(k2_zfmisc_1(X16,X18),k2_zfmisc_1(X17,X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t119_zfmisc_1])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5,X6] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X3,X4))
          & r1_tarski(X2,k2_zfmisc_1(X5,X6)) )
       => r1_tarski(k2_xboole_0(X1,X2),k2_zfmisc_1(k2_xboole_0(X3,X5),k2_xboole_0(X4,X6))) ) ),
    inference(assume_negation,[status(cth)],[t143_zfmisc_1])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0))
    & r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0))
    & ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_13,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_14,plain,(
    ! [X15] : k2_xboole_0(X15,X15) = X15 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k2_xboole_0])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X5))
    | ~ r1_tarski(X5,X3)
    | ~ r1_tarski(X4,X2) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( k2_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk6_0,X2)
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,esk6_0))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

fof(c_0_23,plain,(
    ! [X13,X14] : k2_xboole_0(X13,X14) = k2_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk4_0,X2)
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk6_0,X2)
    | ~ r1_tarski(esk5_0,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_22])).

cnf(c_0_26,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,esk4_0))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,esk6_0))
    | ~ r1_tarski(esk5_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(esk4_0,X2)
    | ~ r1_tarski(esk3_0,X3)
    | ~ r1_tarski(X3,X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,esk6_0))
    | ~ r1_tarski(k2_xboole_0(X2,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,esk4_0))
    | ~ r1_tarski(esk3_0,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(X1,esk5_0),esk6_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,esk4_0))
    | ~ r1_tarski(k2_xboole_0(esk3_0,X2),X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

fof(c_0_35,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_tarski(X31,X30)
      | r1_tarski(k2_xboole_0(X29,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_xboole_0(X3,esk5_0),X1)
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,X1),esk4_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(esk1_0,esk2_0),k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(X1,esk5_0),X2))
    | ~ r1_tarski(esk6_0,X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(X1,X2))
    | ~ r1_tarski(k2_xboole_0(esk3_0,X3),X1)
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0)))
    | ~ r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,k2_zfmisc_1(k2_xboole_0(X1,esk5_0),k2_xboole_0(X2,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,X1),X2))
    | ~ r1_tarski(esk4_0,X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,esk5_0),k2_xboole_0(esk4_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k2_xboole_0(esk3_0,X1),k2_xboole_0(esk4_0,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
