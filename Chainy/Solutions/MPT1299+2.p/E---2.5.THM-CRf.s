%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1299+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:04 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :   22 (  85 expanded)
%              Number of clauses        :   13 (  31 expanded)
%              Number of leaves         :    4 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 277 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t17_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v1_tops_2(X2,X1)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

fof(dt_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => m1_subset_1(k7_setfam_1(X1,X2),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',dt_k7_setfam_1)).

fof(involutiveness_k7_setfam_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => k7_setfam_1(X1,k7_setfam_1(X1,X2)) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/Axioms/MPT006+2.ax',involutiveness_k7_setfam_1)).

fof(t16_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ( v1_tops_2(X2,X1)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_tops_2])).

fof(c_0_5,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X35,k1_zfmisc_1(k1_zfmisc_1(X34)))
      | m1_subset_1(k7_setfam_1(X34,X35),k1_zfmisc_1(k1_zfmisc_1(X34))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_setfam_1])])).

fof(c_0_6,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))
    & ( ~ v1_tops_2(esk2_0,esk1_0)
      | ~ v2_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) )
    & ( v1_tops_2(esk2_0,esk1_0)
      | v2_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

fof(c_0_7,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k1_zfmisc_1(X36)))
      | k7_setfam_1(X36,k7_setfam_1(X36,X37)) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[involutiveness_k7_setfam_1])])).

fof(c_0_8,plain,(
    ! [X27,X28] :
      ( ( ~ v2_tops_2(X28,X27)
        | v1_tops_2(k7_setfam_1(u1_struct_0(X27),X28),X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
        | ~ l1_pre_topc(X27) )
      & ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X27),X28),X27)
        | v2_tops_2(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27))))
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tops_2])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(k7_setfam_1(X2,X1),k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( k7_setfam_1(X2,k7_setfam_1(X2,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v2_tops_2(X2,X1)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( k7_setfam_1(u1_struct_0(esk1_0),k7_setfam_1(u1_struct_0(esk1_0),esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v1_tops_2(esk2_0,esk1_0)
    | v2_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( ~ v1_tops_2(esk2_0,esk1_0)
    | ~ v2_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_19,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(X2),X1),X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( ~ v1_tops_2(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_21,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_18]),c_0_15])]),c_0_20]),
    [proof]).
%------------------------------------------------------------------------------
