%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1292+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:03 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   42 (  67 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 219 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
              & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    & m1_setfam_1(esk6_0,u1_struct_0(esk5_0))
    & esk6_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X19,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k1_zfmisc_1(X19)))
      | k5_setfam_1(X19,X20) = k3_tarski(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X18] :
      ( v2_struct_0(X18)
      | ~ l1_struct_0(X18)
      | ~ v1_xboole_0(u1_struct_0(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ~ m1_subset_1(X21,X22)
      | v1_xboole_0(X22)
      | r2_hidden(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_16,plain,(
    ! [X23,X24] :
      ( ( ~ m1_setfam_1(X24,X23)
        | k5_setfam_1(X23,X24) = X23
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))) )
      & ( k5_setfam_1(X23,X24) != X23
        | m1_setfam_1(X24,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_17,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_setfam_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( k5_setfam_1(u1_struct_0(esk5_0),k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_19,c_0_13])).

fof(c_0_25,plain,(
    ! [X25,X26] :
      ( ~ r2_hidden(X25,X26)
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_26,plain,(
    ! [X5,X6,X7,X9,X10,X11,X12,X14] :
      ( ( r2_hidden(X7,esk1_3(X5,X6,X7))
        | ~ r2_hidden(X7,X6)
        | X6 != k3_tarski(X5) )
      & ( r2_hidden(esk1_3(X5,X6,X7),X5)
        | ~ r2_hidden(X7,X6)
        | X6 != k3_tarski(X5) )
      & ( ~ r2_hidden(X9,X10)
        | ~ r2_hidden(X10,X5)
        | r2_hidden(X9,X6)
        | X6 != k3_tarski(X5) )
      & ( ~ r2_hidden(esk2_2(X11,X12),X12)
        | ~ r2_hidden(esk2_2(X11,X12),X14)
        | ~ r2_hidden(X14,X11)
        | X12 = k3_tarski(X11) )
      & ( r2_hidden(esk2_2(X11,X12),esk3_2(X11,X12))
        | r2_hidden(esk2_2(X11,X12),X12)
        | X12 = k3_tarski(X11) )
      & ( r2_hidden(esk3_2(X11,X12),X11)
        | r2_hidden(esk2_2(X11,X12),X12)
        | X12 = k3_tarski(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( u1_struct_0(esk5_0) = k3_tarski(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_23]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_31,plain,(
    ! [X16] : m1_subset_1(esk4_1(X16),X16) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(k1_xboole_0))
    | ~ m1_subset_1(X1,k3_tarski(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_36,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk4_1(k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_39,c_0_40]),
    [proof]).

%------------------------------------------------------------------------------
