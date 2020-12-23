%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1292+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:03 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   52 (  94 expanded)
%              Number of clauses        :   32 (  43 expanded)
%              Number of leaves         :   10 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 260 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t5_tops_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
              & X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tops_2)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(redefinition_k5_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k5_setfam_1(X1,X2) = k3_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(t60_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( m1_setfam_1(X2,X1)
      <=> k5_setfam_1(X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_10,plain,(
    ! [X29,X30,X31] :
      ( ~ r2_hidden(X29,X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X31))
      | ~ v1_xboole_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_11,plain,(
    ! [X20] : m1_subset_1(esk4_1(X20),X20) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ~ ( m1_setfam_1(X2,u1_struct_0(X1))
                & X2 = k1_xboole_0 ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_tops_2])).

cnf(c_0_13,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk4_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X34] :
      ( ~ v1_xboole_0(X34)
      | X34 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    & m1_setfam_1(esk6_0,u1_struct_0(esk5_0))
    & esk6_0 = k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_17,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_18,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23)))
      | k5_setfam_1(X23,X24) = k3_tarski(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k5_setfam_1])])).

fof(c_0_19,plain,(
    ! [X32,X33] :
      ( ( ~ m1_setfam_1(X33,X32)
        | k5_setfam_1(X32,X33) = X32
        | ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32))) )
      & ( k5_setfam_1(X32,X33) != X32
        | m1_setfam_1(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k1_zfmisc_1(X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_setfam_1])])])).

cnf(c_0_20,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,esk4_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k5_setfam_1(X2,X1) = k3_tarski(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( k5_setfam_1(X2,X1) = X2
    | ~ m1_setfam_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(esk4_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,plain,
    ( X1 = k3_tarski(X2)
    | ~ m1_setfam_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( m1_setfam_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,esk4_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_20])).

fof(c_0_36,plain,(
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

cnf(c_0_37,negated_conjecture,
    ( ~ m1_setfam_1(X1,u1_struct_0(esk5_0))
    | ~ v1_xboole_0(k3_tarski(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_33])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_14])).

cnf(c_0_41,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_21])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])])).

cnf(c_0_45,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_46,plain,
    ( r2_hidden(esk1_3(X1,k3_tarski(X1),X2),X1)
    | ~ r2_hidden(X2,k3_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(X1,k3_tarski(k1_xboole_0))
    | ~ m1_subset_1(X1,k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_29])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,k3_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk4_1(k3_tarski(k1_xboole_0)),k3_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_42])])).

cnf(c_0_51,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_42,c_0_50]),
    [proof]).

%------------------------------------------------------------------------------
