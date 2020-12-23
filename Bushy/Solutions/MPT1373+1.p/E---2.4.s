%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : compts_1__t28_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 239 expanded)
%              Number of clauses        :   32 (  94 expanded)
%              Number of leaves         :    6 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  171 (1201 expanded)
%              Number of equality atoms :   16 ( 145 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_compts_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_compts_1(X3,X1)
                    <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t28_compts_1.p',t28_compts_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t28_compts_1.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t28_compts_1.p',dt_l1_pre_topc)).

fof(t11_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,k2_struct_0(X2))
               => ( v2_compts_1(X3,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X4 = X3
                       => v2_compts_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t28_compts_1.p',t11_compts_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t28_compts_1.p',dt_m1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t28_compts_1.p',t3_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( v2_compts_1(X3,X1)
                      <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_compts_1])).

fof(c_0_7,plain,(
    ! [X11] :
      ( ~ l1_struct_0(X11)
      | k2_struct_0(X11) = u1_struct_0(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_8,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | l1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_9,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & esk3_0 = esk4_0
    & ( ~ v2_compts_1(esk3_0,esk1_0)
      | ~ v2_compts_1(esk4_0,esk2_0) )
    & ( v2_compts_1(esk3_0,esk1_0)
      | v2_compts_1(esk4_0,esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_10,plain,(
    ! [X22,X23,X24,X25] :
      ( ( ~ v2_compts_1(X24,X22)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | X25 != X24
        | v2_compts_1(X25,X23)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(esk9_3(X22,X23,X24),k1_zfmisc_1(u1_struct_0(X23)))
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( esk9_3(X22,X23,X24) = X24
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ v2_compts_1(esk9_3(X22,X23,X24),X23)
        | v2_compts_1(X24,X22)
        | ~ r1_tarski(X24,k2_struct_0(X23))
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_pre_topc(X23,X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

cnf(c_0_11,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_14,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk9_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_22,plain,
    ( esk9_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( v2_compts_1(X1,X2)
    | ~ r1_tarski(X1,u1_struct_0(X3))
    | ~ v2_compts_1(esk9_3(X2,X3,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( esk9_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( v2_compts_1(esk3_0,X1)
    | ~ v2_compts_1(esk9_3(X1,esk2_0,esk3_0),esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( esk9_3(X1,esk2_0,esk3_0) = esk3_0
    | v2_compts_1(esk3_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0)
    | v2_compts_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk1_0)
    | ~ v2_compts_1(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0)
    | ~ v2_compts_1(esk9_3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_35,negated_conjecture,
    ( esk9_3(esk1_0,esk2_0,esk3_0) = esk3_0
    | v2_compts_1(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_36,negated_conjecture,
    ( v2_compts_1(esk3_0,esk2_0)
    | v2_compts_1(esk3_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_16])).

cnf(c_0_37,plain,
    ( v2_compts_1(X1,X2)
    | ~ r1_tarski(X1,k2_struct_0(X2))
    | ~ v2_compts_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk1_0)
    | ~ v2_compts_1(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_40,negated_conjecture,
    ( v2_compts_1(esk3_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_41,plain,
    ( v2_compts_1(X1,X2)
    | ~ r1_tarski(X1,u1_struct_0(X2))
    | ~ v2_compts_1(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_18]),c_0_19]),c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_compts_1(esk3_0,X1)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_42])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_40]),c_0_28]),c_0_27]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
