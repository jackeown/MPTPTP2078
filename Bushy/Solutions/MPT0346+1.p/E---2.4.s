%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : subset_1__t16_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:20 EDT 2019

% Result     : Theorem 0.79s
% Output     : CNFRefutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 633 expanded)
%              Number of clauses        :   55 ( 276 expanded)
%              Number of leaves         :   10 ( 156 expanded)
%              Depth                    :   18
%              Number of atoms          :  233 (2719 expanded)
%              Number of equality atoms :   32 ( 361 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',dt_k9_subset_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',redefinition_k9_subset_1)).

fof(t7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => ( r2_hidden(X4,X2)
                 => r2_hidden(X4,X3) ) )
           => r1_tarski(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',t7_subset_1)).

fof(t16_subset_1,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(X1))
         => ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(X1))
             => ( ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r2_hidden(X5,X2)
                    <=> ( r2_hidden(X5,X3)
                        & r2_hidden(X5,X4) ) ) )
               => X2 = k9_subset_1(X1,X3,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',t16_subset_1)).

fof(idempotence_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',idempotence_k9_subset_1)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',existence_m1_subset_1)).

fof(idempotence_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',idempotence_k3_xboole_0)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',d4_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',commutativity_k3_xboole_0)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t16_subset_1.p',d10_xboole_0)).

fof(c_0_10,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(X29))
      | m1_subset_1(k9_subset_1(X29,X30,X31),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_11,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | k9_subset_1(X38,X39,X40) = k3_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_12,plain,(
    ! [X45,X46,X47] :
      ( ( m1_subset_1(esk7_3(X45,X46,X47),X45)
        | r1_tarski(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( r2_hidden(esk7_3(X45,X46,X47),X46)
        | r1_tarski(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) )
      & ( ~ r2_hidden(esk7_3(X45,X46,X47),X47)
        | r1_tarski(X46,X47)
        | ~ m1_subset_1(X47,k1_zfmisc_1(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(X45)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X1))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(X1))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( r2_hidden(X5,X2)
                      <=> ( r2_hidden(X5,X3)
                          & r2_hidden(X5,X4) ) ) )
                 => X2 = k9_subset_1(X1,X3,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_subset_1])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk7_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_18,negated_conjecture,(
    ! [X10] :
      ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0))
      & ( r2_hidden(X10,esk3_0)
        | ~ r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & ( r2_hidden(X10,esk4_0)
        | ~ r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & ( ~ r2_hidden(X10,esk3_0)
        | ~ r2_hidden(X10,esk4_0)
        | r2_hidden(X10,esk2_0)
        | ~ m1_subset_1(X10,esk1_0) )
      & esk2_0 != k9_subset_1(esk1_0,esk3_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_20,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k9_subset_1(X35,X36,X36) = X36 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[idempotence_k9_subset_1])])).

fof(c_0_21,plain,(
    ! [X32] : m1_subset_1(esk6_1(X32),X32) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | m1_subset_1(esk7_3(X4,X1,k3_xboole_0(X2,X3)),X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X34] : k3_xboole_0(X34,X34) = X34 ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[idempotence_k3_xboole_0])])).

cnf(c_0_25,plain,
    ( r1_tarski(X1,k9_subset_1(X2,X3,X4))
    | r2_hidden(esk7_3(X2,X1,k9_subset_1(X2,X3,X4)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_13])).

cnf(c_0_26,plain,
    ( k9_subset_1(X2,X3,X3) = X3
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk6_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(X1,X2))
    | m1_subset_1(esk7_3(esk1_0,esk2_0,k3_xboole_0(X1,X2)),esk1_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k3_xboole_0(X1,X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(esk2_0,k9_subset_1(esk1_0,X1,X2))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k9_subset_1(esk1_0,X1,X2)),esk2_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_31,plain,
    ( k9_subset_1(X1,X2,X2) = X2 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | m1_subset_1(esk7_3(esk1_0,esk2_0,X1),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk7_3(esk1_0,esk2_0,X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_36,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r2_hidden(X23,X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( r2_hidden(X23,X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(X24,X20)
        | ~ r2_hidden(X24,X21)
        | r2_hidden(X24,X22)
        | X22 != k3_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk5_3(X25,X26,X27),X27)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X25)
        | ~ r2_hidden(esk5_3(X25,X26,X27),X26)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X25)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) )
      & ( r2_hidden(esk5_3(X25,X26,X27),X26)
        | r2_hidden(esk5_3(X25,X26,X27),X27)
        | X27 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk7_3(esk1_0,esk2_0,X1),esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk2_0,X1)
    | r2_hidden(esk7_3(esk1_0,esk2_0,X1),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_33]),c_0_34])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(X1,X2))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k3_xboole_0(X1,X2)),esk3_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_42,plain,(
    ! [X13,X14] : k3_xboole_0(X13,X14) = k3_xboole_0(X14,X13) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_43,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(X1,X2))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k3_xboole_0(X1,X2)),esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk7_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(X1,esk4_0))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k3_xboole_0(X1,esk4_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(X1,esk3_0))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k3_xboole_0(X1,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | r2_hidden(esk7_3(esk1_0,X1,esk2_0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_23])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(esk7_3(X4,X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk7_3(X4,X1,k3_xboole_0(X2,X3)),X2)
    | ~ m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk4_0,X1))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k3_xboole_0(esk4_0,X1)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk3_0,X1))
    | r2_hidden(esk7_3(esk1_0,esk2_0,k3_xboole_0(esk3_0,X1)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,X2),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k3_xboole_0(X1,X2),esk2_0),k3_xboole_0(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_17])).

fof(c_0_56,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk3_0,esk4_0))
    | ~ m1_subset_1(k3_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_48]),c_0_48]),c_0_48]),c_0_23])]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( esk2_0 != k9_subset_1(esk1_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | m1_subset_1(esk7_3(esk1_0,X1,esk2_0),esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_23])).

cnf(c_0_61,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk3_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k3_xboole_0(X1,esk3_0),esk2_0),k3_xboole_0(X1,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_44])).

cnf(c_0_63,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk2_0,k3_xboole_0(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_17]),c_0_41])])).

cnf(c_0_65,negated_conjecture,
    ( k3_xboole_0(esk3_0,esk4_0) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_14]),c_0_41])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | r2_hidden(esk7_3(esk1_0,X1,esk2_0),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,esk2_0),esk3_0)
    | ~ r2_hidden(esk7_3(esk1_0,X1,esk2_0),esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk3_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k3_xboole_0(X1,esk3_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k3_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,k3_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0)
    | ~ m1_subset_1(k3_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_48]),c_0_48]),c_0_48]),c_0_48]),c_0_68])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk4_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k3_xboole_0(X1,esk4_0),esk2_0),k3_xboole_0(X1,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_41])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k3_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0)
    | ~ r2_hidden(esk7_3(esk1_0,k3_xboole_0(esk3_0,esk4_0),esk2_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_17]),c_0_41])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k3_xboole_0(X1,esk4_0),esk2_0)
    | r2_hidden(esk7_3(esk1_0,k3_xboole_0(X1,esk4_0),esk2_0),X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(esk7_3(esk1_0,k3_xboole_0(esk3_0,esk4_0),esk2_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk3_0,esk4_0),k1_zfmisc_1(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_73]),c_0_23])]),c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_17]),c_0_41])]),
    [proof]).
%------------------------------------------------------------------------------
