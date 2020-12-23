%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : setfam_1__t58_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 958 expanded)
%              Number of clauses        :   36 ( 434 expanded)
%              Number of leaves         :    7 ( 241 expanded)
%              Depth                    :   15
%              Number of atoms          :  166 (3929 expanded)
%              Number of equality atoms :   68 (1172 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',t6_boole)).

fof(t58_setfam_1,conjecture,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( r2_hidden(X2,X1)
       => ( r2_hidden(X2,k8_setfam_1(X1,X3))
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
             => r2_hidden(X2,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',t58_setfam_1)).

fof(d10_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( ( X2 != k1_xboole_0
         => k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2) )
        & ( X2 = k1_xboole_0
         => k8_setfam_1(X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',d10_setfam_1)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',dt_o_0_0_xboole_0)).

fof(redefinition_k6_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k6_setfam_1(X1,X2) = k1_setfam_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',redefinition_k6_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',d1_setfam_1)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t58_setfam_1.p',t7_boole)).

fof(c_0_7,plain,(
    ! [X47] :
      ( ~ v1_xboole_0(X47)
      | X47 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
       => ( r2_hidden(X2,X1)
         => ( r2_hidden(X2,k8_setfam_1(X1,X3))
          <=> ! [X4] :
                ( r2_hidden(X4,X3)
               => r2_hidden(X2,X4) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_setfam_1])).

fof(c_0_9,plain,(
    ! [X12,X13] :
      ( ( X13 = k1_xboole_0
        | k8_setfam_1(X12,X13) = k6_setfam_1(X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) )
      & ( X13 != k1_xboole_0
        | k8_setfam_1(X12,X13) = X12
        | ~ m1_subset_1(X13,k1_zfmisc_1(k1_zfmisc_1(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_setfam_1])])])).

cnf(c_0_10,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

fof(c_0_12,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(X33)))
      | k6_setfam_1(X33,X34) = k1_setfam_1(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k6_setfam_1])])).

fof(c_0_13,negated_conjecture,(
    ! [X9] :
      ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0)))
      & r2_hidden(esk2_0,esk1_0)
      & ( r2_hidden(esk4_0,esk3_0)
        | ~ r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0)) )
      & ( ~ r2_hidden(esk2_0,esk4_0)
        | ~ r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0)) )
      & ( r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0))
        | ~ r2_hidden(X9,esk3_0)
        | r2_hidden(esk2_0,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])).

cnf(c_0_14,plain,
    ( X1 = k1_xboole_0
    | k8_setfam_1(X2,X1) = k6_setfam_1(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( k1_xboole_0 = o_0_0_xboole_0 ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k6_setfam_1(X2,X1) = k1_setfam_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X14,X15,X16,X17,X18,X20,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X16,X15)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X16,X17)
        | X15 != k1_setfam_1(X14)
        | X14 = k1_xboole_0 )
      & ( r2_hidden(esk5_3(X14,X15,X18),X14)
        | r2_hidden(X18,X15)
        | X15 != k1_setfam_1(X14)
        | X14 = k1_xboole_0 )
      & ( ~ r2_hidden(X18,esk5_3(X14,X15,X18))
        | r2_hidden(X18,X15)
        | X15 != k1_setfam_1(X14)
        | X14 = k1_xboole_0 )
      & ( r2_hidden(esk7_2(X14,X20),X14)
        | ~ r2_hidden(esk6_2(X14,X20),X20)
        | X20 = k1_setfam_1(X14)
        | X14 = k1_xboole_0 )
      & ( ~ r2_hidden(esk6_2(X14,X20),esk7_2(X14,X20))
        | ~ r2_hidden(esk6_2(X14,X20),X20)
        | X20 = k1_setfam_1(X14)
        | X14 = k1_xboole_0 )
      & ( r2_hidden(esk6_2(X14,X20),X20)
        | ~ r2_hidden(X23,X14)
        | r2_hidden(esk6_2(X14,X20),X23)
        | X20 = k1_setfam_1(X14)
        | X14 = k1_xboole_0 )
      & ( X25 != k1_setfam_1(X24)
        | X25 = k1_xboole_0
        | X24 != k1_xboole_0 )
      & ( X26 != k1_xboole_0
        | X26 = k1_setfam_1(X24)
        | X24 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

cnf(c_0_19,plain,
    ( k8_setfam_1(X1,X2) = k6_setfam_1(X1,X2)
    | X2 = o_0_0_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( k6_setfam_1(esk1_0,esk3_0) = k1_setfam_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk3_0)
    | ~ r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( k8_setfam_1(esk1_0,esk3_0) = k1_setfam_1(esk3_0)
    | esk3_0 = o_0_0_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(esk2_0,esk4_0)
    | ~ r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | X2 = k1_xboole_0
    | ~ r2_hidden(X1,esk5_3(X2,X3,X1))
    | X3 != k1_setfam_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0))
    | r2_hidden(esk2_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(esk5_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_21]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk4_0,esk3_0)
    | ~ r2_hidden(esk2_0,k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk2_0,k1_setfam_1(esk3_0))
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_23])).

cnf(c_0_30,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X2,esk5_3(X1,k1_setfam_1(X1),X2)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_25]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk2_0,esk5_3(esk3_0,k1_setfam_1(esk3_0),X1))
    | r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0))
    | r2_hidden(X1,k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0))
    | ~ r2_hidden(esk2_0,k1_setfam_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_28]),c_0_29])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk2_0,k8_setfam_1(esk1_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_35,plain,
    ( X1 = o_0_0_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk2_0,k1_setfam_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk2_0,X1)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_38,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | r2_hidden(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0
    | ~ r2_hidden(esk2_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_34])).

cnf(c_0_40,plain,
    ( k8_setfam_1(X2,X1) = X2
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( esk3_0 = o_0_0_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])).

cnf(c_0_42,plain,
    ( k8_setfam_1(X1,o_0_0_xboole_0) = X1
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_15]),c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k1_zfmisc_1(esk1_0))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_41])).

fof(c_0_44,plain,(
    ! [X48,X49] :
      ( ~ r2_hidden(X48,X49)
      | ~ v1_xboole_0(X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_45,negated_conjecture,
    ( k8_setfam_1(esk1_0,o_0_0_xboole_0) = esk1_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk4_0,o_0_0_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_41]),c_0_41]),c_0_45]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_11])]),
    [proof]).
%------------------------------------------------------------------------------
