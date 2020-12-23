%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:48 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 889 expanded)
%              Number of clauses        :   44 ( 318 expanded)
%              Number of leaves         :    8 ( 218 expanded)
%              Depth                    :   14
%              Number of atoms          :  258 (6889 expanded)
%              Number of equality atoms :   46 ( 797 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t14_tmap_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_tsep_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t31_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( l1_pre_topc(X3)
             => ! [X4] :
                  ( l1_pre_topc(X4)
                 => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                      & g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
                      & m1_pre_topc(X3,X1) )
                   => m1_pre_topc(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).

fof(c_0_8,plain,(
    ! [X8,X9,X10,X11] :
      ( ( X8 = X10
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) )
      & ( X9 = X11
        | g1_pre_topc(X8,X9) != g1_pre_topc(X10,X11)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_9,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | m1_subset_1(u1_pre_topc(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                 => ( ( v1_tsep_1(X2,X1)
                      & m1_pre_topc(X2,X1) )
                  <=> ( v1_tsep_1(X3,X1)
                      & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_tmap_1])).

cnf(c_0_11,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & esk3_0 = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))
    & ( ~ v1_tsep_1(esk2_0,esk1_0)
      | ~ m1_pre_topc(esk2_0,esk1_0)
      | ~ v1_tsep_1(esk3_0,esk1_0)
      | ~ m1_pre_topc(esk3_0,esk1_0) )
    & ( v1_tsep_1(esk3_0,esk1_0)
      | v1_tsep_1(esk2_0,esk1_0) )
    & ( m1_pre_topc(esk3_0,esk1_0)
      | v1_tsep_1(esk2_0,esk1_0) )
    & ( v1_tsep_1(esk3_0,esk1_0)
      | m1_pre_topc(esk2_0,esk1_0) )
    & ( m1_pre_topc(esk3_0,esk1_0)
      | m1_pre_topc(esk2_0,esk1_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X7] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_15,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( esk3_0 = g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_19,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( u1_pre_topc(esk2_0) = X1
    | g1_pre_topc(X2,X1) != esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( v1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_16]),c_0_20]),c_0_17])])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( u1_pre_topc(esk3_0) = u1_pre_topc(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22])]),c_0_23]),c_0_24])])).

fof(c_0_26,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_tsep_1(X17,X16)
        | ~ m1_pre_topc(X17,X16)
        | v3_pre_topc(X18,X16)
        | X18 != u1_struct_0(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X17,X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( v1_tsep_1(X17,X16)
        | ~ v3_pre_topc(X18,X16)
        | X18 != u1_struct_0(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X17,X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_pre_topc(X17,X16)
        | ~ v3_pre_topc(X18,X16)
        | X18 != u1_struct_0(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ m1_pre_topc(X17,X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_27,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_25]),c_0_24])])).

cnf(c_0_29,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk2_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_25]),c_0_23]),c_0_24])])).

fof(c_0_30,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | m1_subset_1(u1_struct_0(X20),k1_zfmisc_1(u1_struct_0(X19))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_31,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_32,plain,(
    ! [X12,X13,X14,X15] :
      ( ~ l1_pre_topc(X12)
      | ~ l1_pre_topc(X13)
      | ~ l1_pre_topc(X14)
      | ~ l1_pre_topc(X15)
      | g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12)) != g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))
      | g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14)) != g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))
      | ~ m1_pre_topc(X14,X12)
      | m1_pre_topc(X15,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_pre_topc])])])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(esk3_0) = X1
    | g1_pre_topc(X1,X2) != esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_34,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X4)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) != g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0)
    | m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( u1_struct_0(esk3_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_16])).

cnf(c_0_41,plain,
    ( v1_tsep_1(X1,X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]),c_0_35])).

cnf(c_0_42,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]),c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0)
    | m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk3_0
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24]),c_0_39])]),c_0_40]),c_0_25]),c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( v1_tsep_1(esk3_0,X1)
    | ~ v3_pre_topc(u1_struct_0(esk2_0),X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk2_0),X1)
    | ~ v1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0)
    | m1_pre_topc(esk2_0,X1)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_16]),c_0_17])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk2_0,esk1_0)
    | ~ v1_tsep_1(esk3_0,esk1_0)
    | ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( v1_tsep_1(esk3_0,X1)
    | ~ v1_tsep_1(esk2_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( v1_tsep_1(esk2_0,X1)
    | ~ v1_tsep_1(esk3_0,X1)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( v1_tsep_1(esk3_0,esk1_0)
    | v1_tsep_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0)
    | v1_tsep_1(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_tsep_1(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_39])])).

cnf(c_0_55,negated_conjecture,
    ( v1_tsep_1(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_49]),c_0_39])]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk3_0
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_53]),c_0_16]),c_0_17]),c_0_39])])).

cnf(c_0_57,negated_conjecture,
    ( ~ m1_pre_topc(esk2_0,esk1_0)
    | ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(esk3_0,X1)
    | g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_25]),c_0_40]),c_0_16]),c_0_24])])).

cnf(c_0_59,negated_conjecture,
    ( ~ m1_pre_topc(esk3_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_53])])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_58]),c_0_39])]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:11:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.027 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.12/0.37  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.12/0.37  fof(t14_tmap_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_tsep_1(X3,X1)&m1_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tmap_1)).
% 0.12/0.37  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.12/0.37  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.12/0.37  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.12/0.37  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.12/0.37  fof(t31_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(l1_pre_topc(X3)=>![X4]:(l1_pre_topc(X4)=>(((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))&g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))&m1_pre_topc(X3,X1))=>m1_pre_topc(X4,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_pre_topc)).
% 0.12/0.37  fof(c_0_8, plain, ![X8, X9, X10, X11]:((X8=X10|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))&(X9=X11|g1_pre_topc(X8,X9)!=g1_pre_topc(X10,X11)|~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.12/0.37  fof(c_0_9, plain, ![X6]:(~l1_pre_topc(X6)|m1_subset_1(u1_pre_topc(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.12/0.37  fof(c_0_10, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_tsep_1(X3,X1)&m1_pre_topc(X3,X1)))))))), inference(assume_negation,[status(cth)],[t14_tmap_1])).
% 0.12/0.37  cnf(c_0_11, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_12, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  fof(c_0_13, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(esk3_0=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))&((~v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk2_0,esk1_0)|(~v1_tsep_1(esk3_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)))&(((v1_tsep_1(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0))&(m1_pre_topc(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0)))&((v1_tsep_1(esk3_0,esk1_0)|m1_pre_topc(esk2_0,esk1_0))&(m1_pre_topc(esk3_0,esk1_0)|m1_pre_topc(esk2_0,esk1_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.12/0.37  fof(c_0_14, plain, ![X7]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))|(~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X7),u1_pre_topc(X7)))|(~v2_pre_topc(X7)|~l1_pre_topc(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.12/0.37  cnf(c_0_15, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (esk3_0=g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  fof(c_0_18, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.12/0.37  cnf(c_0_19, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (u1_pre_topc(esk2_0)=X1|g1_pre_topc(X2,X1)!=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.12/0.37  cnf(c_0_22, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.37  cnf(c_0_23, negated_conjecture, (v1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_16]), c_0_20]), c_0_17])])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (u1_pre_topc(esk3_0)=u1_pre_topc(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22])]), c_0_23]), c_0_24])])).
% 0.12/0.37  fof(c_0_26, plain, ![X16, X17, X18]:((~v1_tsep_1(X17,X16)|~m1_pre_topc(X17,X16)|v3_pre_topc(X18,X16)|X18!=u1_struct_0(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|~m1_pre_topc(X17,X16)|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((v1_tsep_1(X17,X16)|~v3_pre_topc(X18,X16)|X18!=u1_struct_0(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|~m1_pre_topc(X17,X16)|(~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(m1_pre_topc(X17,X16)|~v3_pre_topc(X18,X16)|X18!=u1_struct_0(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|~m1_pre_topc(X17,X16)|(~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.12/0.37  cnf(c_0_27, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_25]), c_0_24])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk2_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_25]), c_0_23]), c_0_24])])).
% 0.12/0.37  fof(c_0_30, plain, ![X19, X20]:(~l1_pre_topc(X19)|(~m1_pre_topc(X20,X19)|m1_subset_1(u1_struct_0(X20),k1_zfmisc_1(u1_struct_0(X19))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.12/0.37  cnf(c_0_31, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  fof(c_0_32, plain, ![X12, X13, X14, X15]:(~l1_pre_topc(X12)|(~l1_pre_topc(X13)|(~l1_pre_topc(X14)|(~l1_pre_topc(X15)|(g1_pre_topc(u1_struct_0(X12),u1_pre_topc(X12))!=g1_pre_topc(u1_struct_0(X13),u1_pre_topc(X13))|g1_pre_topc(u1_struct_0(X14),u1_pre_topc(X14))!=g1_pre_topc(u1_struct_0(X15),u1_pre_topc(X15))|~m1_pre_topc(X14,X12)|m1_pre_topc(X15,X13)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_pre_topc])])])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (u1_struct_0(esk3_0)=X1|g1_pre_topc(X1,X2)!=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.12/0.37  cnf(c_0_34, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.12/0.37  cnf(c_0_35, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.37  cnf(c_0_36, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_31])).
% 0.12/0.37  cnf(c_0_37, plain, (m1_pre_topc(X4,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X4)|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))!=g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)|m1_pre_topc(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (u1_struct_0(esk3_0)=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_33, c_0_16])).
% 0.12/0.37  cnf(c_0_41, plain, (v1_tsep_1(X1,X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_34]), c_0_35])).
% 0.12/0.37  cnf(c_0_42, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_36]), c_0_35])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)|m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=esk3_0|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_24]), c_0_39])]), c_0_40]), c_0_25]), c_0_16])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (v1_tsep_1(esk3_0,X1)|~v3_pre_topc(u1_struct_0(esk2_0),X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_40])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (v3_pre_topc(u1_struct_0(esk2_0),X1)|~v1_tsep_1(esk3_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_42, c_0_40])).
% 0.12/0.37  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)|m1_pre_topc(esk2_0,X1)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_16]), c_0_17])])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (~v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk2_0,esk1_0)|~v1_tsep_1(esk3_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (v1_tsep_1(esk3_0,X1)|~v1_tsep_1(esk2_0,X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(esk2_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_44, c_0_42])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (v1_tsep_1(esk2_0,X1)|~v1_tsep_1(esk3_0,X1)|~m1_pre_topc(esk2_0,X1)|~m1_pre_topc(esk3_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_45])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (v1_tsep_1(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)|v1_tsep_1(esk2_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk2_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_46]), c_0_39])])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (~v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk2_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_39])])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (v1_tsep_1(esk2_0,esk1_0)|~m1_pre_topc(esk2_0,esk1_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_49]), c_0_39])]), c_0_52])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (m1_pre_topc(X1,X2)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=esk3_0|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_53]), c_0_16]), c_0_17]), c_0_39])])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (~m1_pre_topc(esk2_0,esk1_0)|~m1_pre_topc(esk3_0,esk1_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (m1_pre_topc(esk3_0,X1)|g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_25]), c_0_40]), c_0_16]), c_0_24])])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (~m1_pre_topc(esk3_0,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_53])])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_58]), c_0_39])]), c_0_59]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 61
% 0.12/0.37  # Proof object clause steps            : 44
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 34
% 0.12/0.37  # Proof object clause conjectures      : 31
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 19
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 21
% 0.12/0.37  # Proof object simplifying inferences  : 50
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 23
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 22
% 0.12/0.37  # Processed clauses                    : 108
% 0.12/0.37  # ...of these trivial                  : 4
% 0.12/0.37  # ...subsumed                          : 17
% 0.12/0.37  # ...remaining for further processing  : 87
% 0.12/0.37  # Other redundant clauses eliminated   : 13
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 3
% 0.12/0.37  # Backward-rewritten                   : 17
% 0.12/0.37  # Generated clauses                    : 129
% 0.12/0.37  # ...of the previous two non-trivial   : 88
% 0.12/0.37  # Contextual simplify-reflections      : 3
% 0.12/0.37  # Paramodulations                      : 110
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 18
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 42
% 0.12/0.37  #    Positive orientable unit clauses  : 13
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 28
% 0.12/0.37  # Current number of unprocessed clauses: 16
% 0.12/0.37  # ...number of literals in the above   : 81
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 43
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 303
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 110
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 23
% 0.12/0.37  # Unit Clause-clause subsumption calls : 12
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 3
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4218
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.030 s
% 0.12/0.37  # System time              : 0.006 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
