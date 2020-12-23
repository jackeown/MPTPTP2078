%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0346+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:39:27 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 235 expanded)
%              Number of clauses        :   48 (  98 expanded)
%              Number of leaves         :    6 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  211 (1334 expanded)
%              Number of equality atoms :   23 ( 133 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X26,X27,X28] :
      ( ( m1_subset_1(esk2_3(X26,X27,X28),X26)
        | r1_tarski(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( r2_hidden(esk2_3(X26,X27,X28),X27)
        | r1_tarski(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) )
      & ( ~ r2_hidden(esk2_3(X26,X27,X28),X28)
        | r1_tarski(X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(X26))
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_subset_1])])])])])).

fof(c_0_8,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(X19))
      | m1_subset_1(k9_subset_1(X19,X20,X21),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

fof(c_0_9,negated_conjecture,(
    ! [X34] :
      ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0))
      & ( r2_hidden(X34,esk5_0)
        | ~ r2_hidden(X34,esk4_0)
        | ~ m1_subset_1(X34,esk3_0) )
      & ( r2_hidden(X34,esk6_0)
        | ~ r2_hidden(X34,esk4_0)
        | ~ m1_subset_1(X34,esk3_0) )
      & ( ~ r2_hidden(X34,esk5_0)
        | ~ r2_hidden(X34,esk6_0)
        | r2_hidden(X34,esk4_0)
        | ~ m1_subset_1(X34,esk3_0) )
      & esk4_0 != k9_subset_1(esk3_0,esk5_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_10,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),X1)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_tarski(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk2_3(X1,X2,k9_subset_1(X1,X3,X4)),X1)
    | r1_tarski(X2,k9_subset_1(X1,X3,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_3(X1,X2,k9_subset_1(X1,X3,X4)),X2)
    | r1_tarski(X2,k9_subset_1(X1,X3,X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,X1,esk4_0),X1)
    | r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_17,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( r2_hidden(X13,X10)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( r2_hidden(X13,X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(X14,X10)
        | ~ r2_hidden(X14,X11)
        | r2_hidden(X14,X12)
        | X12 != k3_xboole_0(X10,X11) )
      & ( ~ r2_hidden(esk1_3(X15,X16,X17),X17)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X15)
        | ~ r2_hidden(esk1_3(X15,X16,X17),X16)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X15)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) )
      & ( r2_hidden(esk1_3(X15,X16,X17),X16)
        | r2_hidden(esk1_3(X15,X16,X17),X17)
        | X17 = k3_xboole_0(X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k9_subset_1(esk3_0,X1,X2)),esk3_0)
    | r1_tarski(esk4_0,k9_subset_1(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_20,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k9_subset_1(esk3_0,X1,X2)),esk4_0)
    | r1_tarski(esk4_0,k9_subset_1(esk3_0,X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,X1,esk4_0),esk3_0)
    | r1_tarski(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_10,c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k9_subset_1(esk3_0,X1,X2),esk4_0),k9_subset_1(esk3_0,X1,X2))
    | r1_tarski(k9_subset_1(esk3_0,X1,X2),esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_11])).

fof(c_0_23,plain,(
    ! [X23,X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(X23))
      | k9_subset_1(X23,X24,X25) = k3_xboole_0(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,k9_subset_1(esk3_0,X1,esk6_0)),esk3_0)
    | r1_tarski(esk4_0,k9_subset_1(esk3_0,X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k9_subset_1(esk3_0,X1,esk6_0)),esk4_0)
    | r1_tarski(esk4_0,k9_subset_1(esk3_0,X1,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k9_subset_1(esk3_0,X1,X2),esk4_0),esk3_0)
    | r1_tarski(k9_subset_1(esk3_0,X1,X2),esk4_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_11])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k9_subset_1(esk3_0,X1,esk6_0),esk4_0),k9_subset_1(esk3_0,X1,esk6_0))
    | r1_tarski(k9_subset_1(esk3_0,X1,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_19])).

cnf(c_0_31,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( r1_tarski(X2,X3)
    | ~ r2_hidden(esk2_3(X1,X2,X3),X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k9_subset_1(esk3_0,X1,esk6_0)),esk6_0)
    | r1_tarski(esk4_0,k9_subset_1(esk3_0,X1,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk4_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k9_subset_1(esk3_0,X1,esk6_0),esk4_0),esk3_0)
    | r1_tarski(k9_subset_1(esk3_0,X1,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_37,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k3_xboole_0(X1,esk6_0),esk4_0),k3_xboole_0(X1,esk6_0))
    | r1_tarski(k3_xboole_0(X1,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_19])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ r2_hidden(esk2_3(X4,X1,k3_xboole_0(X2,X3)),X3)
    | ~ r2_hidden(esk2_3(X4,X1,k3_xboole_0(X2,X3)),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k3_xboole_0(X1,esk6_0)),esk6_0)
    | r1_tarski(esk4_0,k3_xboole_0(X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_19])])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k9_subset_1(esk3_0,X1,esk6_0)),esk5_0)
    | r1_tarski(esk4_0,k9_subset_1(esk3_0,X1,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_26]),c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,k3_xboole_0(X1,esk6_0),esk4_0),esk3_0)
    | r1_tarski(k3_xboole_0(X1,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_19])])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k3_xboole_0(X1,esk6_0),esk4_0),esk6_0)
    | r1_tarski(k3_xboole_0(X1,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_48,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(X1,esk6_0))
    | ~ m1_subset_1(k3_xboole_0(X1,esk6_0),k1_zfmisc_1(esk3_0))
    | ~ r2_hidden(esk2_3(esk3_0,esk4_0,k3_xboole_0(X1,esk6_0)),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_13])])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,esk4_0,k3_xboole_0(X1,esk6_0)),esk5_0)
    | r1_tarski(esk4_0,k3_xboole_0(X1,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_31]),c_0_19])])).

cnf(c_0_50,negated_conjecture,
    ( esk4_0 != k9_subset_1(esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k3_xboole_0(X1,esk6_0),esk4_0),esk4_0)
    | r1_tarski(k3_xboole_0(X1,esk6_0),esk4_0)
    | ~ r2_hidden(esk2_3(esk3_0,k3_xboole_0(X1,esk6_0),esk4_0),esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k3_xboole_0(X1,esk6_0),esk4_0),X1)
    | r1_tarski(k3_xboole_0(X1,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_53,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk4_0,k3_xboole_0(esk5_0,esk6_0))
    | ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( k3_xboole_0(esk5_0,esk6_0) != esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_31]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk2_3(esk3_0,k3_xboole_0(esk5_0,esk6_0),esk4_0),esk4_0)
    | r1_tarski(k3_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0))
    | ~ r1_tarski(k3_xboole_0(esk5_0,esk6_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(esk5_0,esk6_0),k1_zfmisc_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_56]),c_0_13])]),c_0_57])).

cnf(c_0_59,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(spm,[status(thm)],[c_0_11,c_0_31])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
