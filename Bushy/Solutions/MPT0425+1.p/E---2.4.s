%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t57_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   53 (  84 expanded)
%              Number of clauses        :   30 (  37 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :   94 ( 157 expanded)
%              Number of equality atoms :   25 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t57_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))
        & ! [X4] :
            ( r2_hidden(X4,X2)
           => r1_xboole_0(X4,X3) ) )
     => r1_tarski(X3,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t57_setfam_1)).

fof(t98_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_xboole_0(X3,X2) )
     => r1_xboole_0(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t98_zfmisc_1)).

fof(d7_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k3_xboole_0(X1,X2) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',d7_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',commutativity_k3_xboole_0)).

fof(t96_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t96_zfmisc_1)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t19_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t17_xboole_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',idempotence_k3_xboole_0)).

fof(t23_xboole_1,axiom,(
    ! [X1,X2,X3] : k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t23_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t1_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t57_setfam_1.p',t1_boole)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( r1_tarski(X3,k3_tarski(k2_xboole_0(X1,X2)))
          & ! [X4] :
              ( r2_hidden(X4,X2)
             => r1_xboole_0(X4,X3) ) )
       => r1_tarski(X3,k3_tarski(X1)) ) ),
    inference(assume_negation,[status(cth)],[t57_setfam_1])).

fof(c_0_12,negated_conjecture,(
    ! [X8] :
      ( r1_tarski(esk3_0,k3_tarski(k2_xboole_0(esk1_0,esk2_0)))
      & ( ~ r2_hidden(X8,esk2_0)
        | r1_xboole_0(X8,esk3_0) )
      & ~ r1_tarski(esk3_0,k3_tarski(esk1_0)) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_13,plain,(
    ! [X55,X56] :
      ( ( r2_hidden(esk5_2(X55,X56),X55)
        | r1_xboole_0(k3_tarski(X55),X56) )
      & ( ~ r1_xboole_0(esk5_2(X55,X56),X56)
        | r1_xboole_0(k3_tarski(X55),X56) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_zfmisc_1])])])])).

fof(c_0_14,plain,(
    ! [X15,X16] :
      ( ( ~ r1_xboole_0(X15,X16)
        | k3_xboole_0(X15,X16) = k1_xboole_0 )
      & ( k3_xboole_0(X15,X16) != k1_xboole_0
        | r1_xboole_0(X15,X16) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_xboole_0])])).

cnf(c_0_15,negated_conjecture,
    ( r1_xboole_0(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r1_xboole_0(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k3_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_18,plain,(
    ! [X53,X54] : k3_tarski(k2_xboole_0(X53,X54)) = k2_xboole_0(k3_tarski(X53),k3_tarski(X54)) ),
    inference(variable_rename,[status(thm)],[t96_zfmisc_1])).

cnf(c_0_19,plain,
    ( k3_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( r1_xboole_0(esk5_2(esk2_0,X1),esk3_0)
    | r1_xboole_0(k3_tarski(esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_23,plain,(
    ! [X25,X26,X27] :
      ( ~ r1_tarski(X25,X26)
      | ~ r1_tarski(X25,X27)
      | r1_tarski(X25,k3_xboole_0(X26,X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,k3_tarski(k2_xboole_0(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_xboole_0(X1,X2)) = k2_xboole_0(k3_tarski(X1),k3_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_26,plain,(
    ! [X23,X24] : r1_tarski(k3_xboole_0(X23,X24),X23) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_27,plain,(
    ! [X20] : k3_xboole_0(X20,X20) = X20 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

fof(c_0_28,plain,(
    ! [X34,X35,X36] : k3_xboole_0(X34,k2_xboole_0(X35,X36)) = k2_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X34,X36)) ),
    inference(variable_rename,[status(thm)],[t23_xboole_1])).

cnf(c_0_29,plain,
    ( r1_xboole_0(k3_tarski(X1),X2)
    | ~ r1_xboole_0(esk5_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k3_xboole_0(k3_tarski(esk2_0),X1) = k1_xboole_0
    | r1_xboole_0(esk5_2(esk2_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_32,plain,(
    ! [X31,X32,X33] :
      ( ~ r1_tarski(X31,X32)
      | ~ r1_tarski(X32,X33)
      | r1_tarski(X31,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk3_0,k2_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X3)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( r1_xboole_0(k3_tarski(esk2_0),esk3_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_22]),c_0_31])).

fof(c_0_39,plain,(
    ! [X28] : k2_xboole_0(X28,k1_xboole_0) = X28 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(X1,k2_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0))))
    | ~ r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k2_xboole_0(X1,X3)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( k3_xboole_0(esk3_0,k3_tarski(esk2_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_38]),c_0_22])).

cnf(c_0_45,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk3_0,k2_xboole_0(k3_tarski(esk1_0),k3_tarski(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk3_0,k2_xboole_0(X1,k3_tarski(esk2_0))) = k3_xboole_0(X1,esk3_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k3_xboole_0(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_22])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk3_0,k3_xboole_0(esk3_0,k3_tarski(esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48]),c_0_22])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tarski(esk3_0,k3_tarski(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),
    [proof]).
%------------------------------------------------------------------------------
