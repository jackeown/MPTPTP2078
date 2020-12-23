%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tops_2__t16_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 486 expanded)
%              Number of clauses        :   44 ( 188 expanded)
%              Number of leaves         :    9 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  258 (2122 expanded)
%              Number of equality atoms :   10 (  47 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',d1_tops_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',t4_subset)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',dt_k7_setfam_1)).

fof(t16_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',t16_tops_2)).

fof(d8_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
         => ( X3 = k7_setfam_1(X1,X2)
          <=> ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(X1))
               => ( r2_hidden(X4,X3)
                <=> r2_hidden(k3_subset_1(X1,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',d8_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',involutiveness_k7_setfam_1)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',d2_tops_2)).

fof(t29_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v4_pre_topc(X2,X1)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',t29_tops_1)).

fof(t30_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t16_tops_2.p',t30_tops_1)).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v1_tops_2(X10,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(X11,X10)
        | v3_pre_topc(X11,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | v1_tops_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_2(X9,X10),X10)
        | v1_tops_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) )
      & ( ~ v3_pre_topc(esk3_2(X9,X10),X9)
        | v1_tops_2(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tops_2])])])])])).

fof(c_0_10,plain,(
    ! [X47,X48,X49] :
      ( ~ r2_hidden(X47,X48)
      | ~ m1_subset_1(X48,k1_zfmisc_1(X49))
      | m1_subset_1(X47,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_11,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k1_zfmisc_1(X24)))
      | m1_subset_1(k7_setfam_1(X24,X25),k1_zfmisc_1(k1_zfmisc_1(X24))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v2_tops_2(X2,X1)
            <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_tops_2])).

cnf(c_0_15,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v1_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ( ~ v2_tops_2(esk2_0,esk1_0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) )
    & ( v2_tops_2(esk2_0,esk1_0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_18,plain,(
    ! [X17,X18,X19,X20] :
      ( ( ~ r2_hidden(X20,X19)
        | r2_hidden(k3_subset_1(X17,X20),X18)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X17))
        | X19 != k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( ~ r2_hidden(k3_subset_1(X17,X20),X18)
        | r2_hidden(X20,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(X17))
        | X19 != k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( m1_subset_1(esk5_3(X17,X18,X19),k1_zfmisc_1(X17))
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( ~ r2_hidden(esk5_3(X17,X18,X19),X19)
        | ~ r2_hidden(k3_subset_1(X17,esk5_3(X17,X18,X19)),X18)
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( r2_hidden(esk5_3(X17,X18,X19),X19)
        | r2_hidden(k3_subset_1(X17,esk5_3(X17,X18,X19)),X18)
        | X19 = k7_setfam_1(X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X17)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_setfam_1])])])])])).

cnf(c_0_19,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(X2),X3))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X2),X3),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r2_hidden(k3_subset_1(X3,X1),X4)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | X2 != k7_setfam_1(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_23,plain,(
    ! [X33,X34] :
      ( ~ m1_subset_1(X34,k1_zfmisc_1(k1_zfmisc_1(X33)))
      | k7_setfam_1(X33,k7_setfam_1(X33,X34)) = X34 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

cnf(c_0_24,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_25,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( r2_hidden(k3_subset_1(X1,X2),X3)
    | ~ r2_hidden(X2,k7_setfam_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_22,c_0_12])]),c_0_16])).

cnf(c_0_27,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_28,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v2_tops_2(X14,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X15,X14)
        | v4_pre_topc(X15,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk4_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))
        | v2_tops_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk4_2(X13,X14),X14)
        | v2_tops_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ l1_pre_topc(X13) )
      & ( ~ v4_pre_topc(esk4_2(X13,X14),X13)
        | v2_tops_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_29,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | v2_tops_2(esk2_0,esk1_0)
    | ~ r2_hidden(X1,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X3))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_32,plain,(
    ! [X37,X38] :
      ( ( ~ v4_pre_topc(X38,X37)
        | v3_pre_topc(k3_subset_1(u1_struct_0(X37),X38),X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_pre_topc(X37) )
      & ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X37),X38),X37)
        | v4_pre_topc(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ l1_pre_topc(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_tops_1])])])])).

cnf(c_0_33,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk1_0),X1),esk1_0)
    | v2_tops_2(esk2_0,esk1_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_20])])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk4_2(esk1_0,esk2_0),esk2_0)
    | v2_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_20]),c_0_21])])).

cnf(c_0_35,plain,
    ( m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( v4_pre_topc(X2,X1)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(esk1_0),esk4_2(esk1_0,esk2_0)),esk1_0)
    | v2_tops_2(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0)
    | m1_subset_1(esk4_2(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_21])])).

cnf(c_0_39,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk4_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(esk4_2(esk1_0,esk2_0),esk1_0)
    | v2_tops_2(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_21])]),c_0_38])).

fof(c_0_43,plain,(
    ! [X41,X42] :
      ( ( ~ v3_pre_topc(X42,X41)
        | v4_pre_topc(k3_subset_1(u1_struct_0(X41),X42),X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) )
      & ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X41),X42),X41)
        | v3_pre_topc(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_tops_1])])])])).

cnf(c_0_44,plain,
    ( v4_pre_topc(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ v2_tops_2(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_39,c_0_12])).

cnf(c_0_45,plain,
    ( r2_hidden(esk3_2(X1,k7_setfam_1(u1_struct_0(X1),X2)),k7_setfam_1(u1_struct_0(X1),X2))
    | v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_tops_2(esk2_0,esk1_0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( v2_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_20]),c_0_21])])).

cnf(c_0_48,plain,
    ( v3_pre_topc(X2,X1)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( v4_pre_topc(X1,esk1_0)
    | ~ r2_hidden(X1,esk2_0)
    | ~ v2_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_21])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk3_2(esk1_0,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),k7_setfam_1(u1_struct_0(esk1_0),esk2_0))
    | v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_20]),c_0_21])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47])])).

cnf(c_0_52,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k7_setfam_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_12,c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk1_0),X1),esk2_0)
    | ~ v2_tops_2(esk2_0,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_21])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk3_2(esk1_0,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) ),
    inference(sr,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | m1_subset_1(esk3_2(esk1_0,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_20])])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(X1,esk1_0)
    | ~ r2_hidden(k3_subset_1(u1_struct_0(esk1_0),X1),esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k3_subset_1(u1_struct_0(esk1_0),esk3_2(esk1_0,k7_setfam_1(u1_struct_0(esk1_0),esk2_0))),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_54]),c_0_20])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk3_2(esk1_0,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[c_0_55,c_0_51])).

cnf(c_0_59,plain,
    ( v1_tops_2(X2,X1)
    | ~ v3_pre_topc(esk3_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk3_2(esk1_0,k7_setfam_1(u1_struct_0(esk1_0),esk2_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58])])).

cnf(c_0_61,negated_conjecture,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_21])]),c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_16]),c_0_20])]),
    [proof]).
%------------------------------------------------------------------------------
