%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1135+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:02 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 290 expanded)
%              Number of clauses        :   36 ( 116 expanded)
%              Number of leaves         :   11 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  147 ( 921 expanded)
%              Number of equality atoms :   33 ( 252 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
             => ( X2 = X3
               => g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
               => ( X2 = X3
                 => g1_pre_topc(u1_struct_0(k1_pre_topc(X1,X2)),u1_pre_topc(k1_pre_topc(X1,X2))) = k1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_pre_topc])).

fof(c_0_12,plain,(
    ! [X96] :
      ( ~ l1_pre_topc(X96)
      | m1_subset_1(u1_pre_topc(X96),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X96)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    & esk2_0 = esk3_0
    & g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])).

fof(c_0_14,plain,(
    ! [X46,X47] :
      ( ( v1_pre_topc(g1_pre_topc(X46,X47))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X46))) )
      & ( l1_pre_topc(g1_pre_topc(X46,X47))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k1_zfmisc_1(X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X27,X28] :
      ( ( v1_pre_topc(k1_pre_topc(X27,X28))
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( m1_pre_topc(k1_pre_topc(X27,X28),X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( esk2_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_22,plain,(
    ! [X352,X353] :
      ( ~ l1_pre_topc(X352)
      | ~ m1_pre_topc(X353,X352)
      | l1_pre_topc(X353) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_23,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_26,plain,(
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))
      | u1_struct_0(k1_pre_topc(X39,X40)) = X40 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_28,plain,(
    ! [X351] :
      ( ~ l1_pre_topc(X351)
      | l1_struct_0(X351) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_29,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X45] :
      ( ~ l1_pre_topc(X45)
      | ~ v1_pre_topc(X45)
      | X45 = g1_pre_topc(u1_struct_0(X45),u1_pre_topc(X45)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk1_0,esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_27]),c_0_16])])).

cnf(c_0_35,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_36,plain,(
    ! [X24,X25,X26] :
      ( ( X26 != k1_pre_topc(X24,X25)
        | k2_struct_0(X26) = X25
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) )
      & ( k2_struct_0(X26) != X25
        | X26 = k1_pre_topc(X24,X25)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_37,plain,(
    ! [X59,X60] :
      ( ~ l1_pre_topc(X59)
      | ~ m1_pre_topc(X60,g1_pre_topc(u1_struct_0(X59),u1_pre_topc(X59)))
      | m1_pre_topc(X60,X59) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

fof(c_0_38,plain,(
    ! [X101] :
      ( ~ l1_struct_0(X101)
      | k2_struct_0(X101) = u1_struct_0(X101) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_39,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_25])])).

cnf(c_0_41,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(esk1_0,esk2_0)),u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) != k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_19])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(esk1_0,esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_16])])).

cnf(c_0_43,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_34]),c_0_16])])).

cnf(c_0_45,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_16])])).

cnf(c_0_46,plain,
    ( X1 = k1_pre_topc(X3,X2)
    | k2_struct_0(X1) != X2
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( l1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) = esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_24]),c_0_25])])).

cnf(c_0_51,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) != g1_pre_topc(esk2_0,u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( g1_pre_topc(esk2_0,u1_pre_topc(k1_pre_topc(esk1_0,esk2_0))) = k1_pre_topc(esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_42]),c_0_45])])).

cnf(c_0_53,plain,
    ( k1_pre_topc(X1,k2_struct_0(X2)) = X2
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_16])])).

cnf(c_0_55,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_24]),c_0_25])])).

cnf(c_0_57,negated_conjecture,
    ( k1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) != k1_pre_topc(esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_16]),c_0_55]),c_0_27])]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
