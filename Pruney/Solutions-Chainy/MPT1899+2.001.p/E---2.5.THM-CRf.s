%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   58 (1728 expanded)
%              Number of clauses        :   41 ( 558 expanded)
%              Number of leaves         :    8 ( 431 expanded)
%              Depth                    :   11
%              Number of atoms          :  321 (14584 expanded)
%              Number of equality atoms :   13 ( 132 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( v2_tex_2(X3,X1)
                <=> v1_tdlat_3(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t67_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v1_tdlat_3(X2)
            & m1_pre_topc(X2,X1) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & m1_pre_topc(X2,X3)
              & v4_tex_2(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tex_2)).

fof(t65_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ~ ( v2_tex_2(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ~ ( r1_tarski(X2,X3)
                      & v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(t46_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ v3_tex_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(t10_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ? [X3] :
              ( ~ v2_struct_0(X3)
              & v1_pre_topc(X3)
              & m1_pre_topc(X3,X1)
              & X2 = u1_struct_0(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(d8_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v4_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(c_0_8,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v2_tex_2(X18,X16)
        | v1_tdlat_3(X17)
        | X18 != u1_struct_0(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ v1_tdlat_3(X17)
        | v2_tex_2(X18,X16)
        | X18 != u1_struct_0(X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X16)
        | v2_struct_0(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_9,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X5,X4)
      | m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2)
              & m1_pre_topc(X2,X1) )
           => ? [X3] :
                ( ~ v2_struct_0(X3)
                & v1_pre_topc(X3)
                & m1_pre_topc(X3,X1)
                & m1_pre_topc(X2,X3)
                & v4_tex_2(X3,X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_tex_2])).

fof(c_0_11,plain,(
    ! [X21,X22] :
      ( ( m1_subset_1(esk3_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_tex_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ v3_tdlat_3(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(X22,esk3_2(X21,X22))
        | ~ v2_tex_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ v3_tdlat_3(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_tex_2(esk3_2(X21,X22),X21)
        | ~ v2_tex_2(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ v3_tdlat_3(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_12,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,(
    ! [X26] :
      ( ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & v3_tdlat_3(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & v1_tdlat_3(esk5_0)
      & m1_pre_topc(esk5_0,esk4_0)
      & ( v2_struct_0(X26)
        | ~ v1_pre_topc(X26)
        | ~ m1_pre_topc(X26,esk4_0)
        | ~ m1_pre_topc(esk5_0,X26)
        | ~ v4_tex_2(X26,esk4_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]),c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( v1_tdlat_3(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( v3_tex_2(esk3_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ v1_xboole_0(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | ~ v3_tex_2(X20,X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk3_2(X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_tex_2(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk5_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( v3_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
    ( v3_tex_2(esk3_2(X1,u1_struct_0(X2)),X1)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_tex_2(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_13])).

fof(c_0_29,plain,(
    ! [X13,X14] :
      ( ( ~ v2_struct_0(esk2_2(X13,X14))
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) )
      & ( v1_pre_topc(esk2_2(X13,X14))
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_pre_topc(esk2_2(X13,X14),X13)
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) )
      & ( X14 = u1_struct_0(esk2_2(X13,X14))
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk3_2(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_17]),c_0_19])]),c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v3_tex_2(esk3_2(esk4_0,u1_struct_0(esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26]),c_0_27]),c_0_17]),c_0_19])]),c_0_21])).

fof(c_0_33,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v4_tex_2(X10,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | X11 != u1_struct_0(X10)
        | v3_tex_2(X11,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | v4_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( esk1_2(X9,X10) = u1_struct_0(X10)
        | v4_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ v3_tex_2(esk1_2(X9,X10),X9)
        | v4_tex_2(X10,X9)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).

cnf(c_0_34,plain,
    ( m1_pre_topc(esk2_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(esk3_2(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_27]),c_0_19])]),c_0_21])).

cnf(c_0_36,plain,
    ( X1 = u1_struct_0(esk2_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( v1_pre_topc(esk2_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk2_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( esk1_2(X1,X2) = u1_struct_0(X2)
    | v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_19])]),c_0_21]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0)))) = esk3_2(esk4_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_31]),c_0_19])]),c_0_21]),c_0_35])).

fof(c_0_42,plain,(
    ! [X6,X7,X8] :
      ( ( ~ r1_tarski(u1_struct_0(X7),u1_struct_0(X8))
        | m1_pre_topc(X7,X8)
        | ~ m1_pre_topc(X8,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ m1_pre_topc(X7,X8)
        | r1_tarski(u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_pre_topc(X8,X6)
        | ~ m1_pre_topc(X7,X6)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_43,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ v4_tex_2(X1,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,negated_conjecture,
    ( v1_pre_topc(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_19])]),c_0_21]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_19])]),c_0_21]),c_0_35])).

cnf(c_0_46,plain,
    ( v4_tex_2(X2,X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(esk1_2(X1,X2),X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( esk1_2(esk4_0,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0)))) = esk3_2(esk4_0,u1_struct_0(esk5_0))
    | v4_tex_2(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_19])]),c_0_21]),c_0_41])).

cnf(c_0_48,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,esk3_2(X2,X1))
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v3_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( ~ v4_tex_2(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0)
    | ~ m1_pre_topc(esk5_0,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_40])])).

cnf(c_0_51,negated_conjecture,
    ( v4_tex_2(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32]),c_0_40]),c_0_19])]),c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(X1,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))
    | ~ r1_tarski(u1_struct_0(X1),esk3_2(esk4_0,u1_struct_0(esk5_0)))
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_48,c_0_41])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(X2),esk3_2(X1,u1_struct_0(X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_tex_2(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_13])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_pre_topc(esk5_0,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_55,negated_conjecture,
    ( m1_pre_topc(X1,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))
    | ~ r1_tarski(u1_struct_0(X1),esk3_2(esk4_0,u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_40]),c_0_27]),c_0_19])])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk5_0),esk3_2(esk4_0,u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_25]),c_0_26]),c_0_27]),c_0_17]),c_0_19])]),c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_17])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.029 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 0.19/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.39  fof(t67_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>?[X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&m1_pre_topc(X2,X3))&v4_tex_2(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tex_2)).
% 0.19/0.39  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 0.19/0.39  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.19/0.39  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.19/0.39  fof(d8_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(v4_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v3_tex_2(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 0.19/0.39  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.19/0.39  fof(c_0_8, plain, ![X16, X17, X18]:((~v2_tex_2(X18,X16)|v1_tdlat_3(X17)|X18!=u1_struct_0(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~l1_pre_topc(X16)))&(~v1_tdlat_3(X17)|v2_tex_2(X18,X16)|X18!=u1_struct_0(X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X17)|~m1_pre_topc(X17,X16))|(v2_struct_0(X16)|~l1_pre_topc(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.19/0.39  fof(c_0_9, plain, ![X4, X5]:(~l1_pre_topc(X4)|(~m1_pre_topc(X5,X4)|m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X4))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>?[X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&m1_pre_topc(X2,X3))&v4_tex_2(X3,X1))))), inference(assume_negation,[status(cth)],[t67_tex_2])).
% 0.19/0.39  fof(c_0_11, plain, ![X21, X22]:((m1_subset_1(esk3_2(X21,X22),k1_zfmisc_1(u1_struct_0(X21)))|~v2_tex_2(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~v3_tdlat_3(X21)|~l1_pre_topc(X21)))&((r1_tarski(X22,esk3_2(X21,X22))|~v2_tex_2(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~v3_tdlat_3(X21)|~l1_pre_topc(X21)))&(v3_tex_2(esk3_2(X21,X22),X21)|~v2_tex_2(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~v3_tdlat_3(X21)|~l1_pre_topc(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.19/0.39  cnf(c_0_12, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_13, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  fof(c_0_14, negated_conjecture, ![X26]:((((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&v3_tdlat_3(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v1_tdlat_3(esk5_0))&m1_pre_topc(esk5_0,esk4_0))&(v2_struct_0(X26)|~v1_pre_topc(X26)|~m1_pre_topc(X26,esk4_0)|~m1_pre_topc(esk5_0,X26)|~v4_tex_2(X26,esk4_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 0.19/0.39  cnf(c_0_15, plain, (m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_16, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_12]), c_0_13])).
% 0.19/0.39  cnf(c_0_17, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (v1_tdlat_3(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_22, plain, (v3_tex_2(esk3_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  fof(c_0_23, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~v1_xboole_0(X20)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|~v3_tex_2(X20,X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.19/0.39  cnf(c_0_24, plain, (v2_struct_0(X1)|m1_subset_1(esk3_2(X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X1)))|~v3_tdlat_3(X1)|~v2_tex_2(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_15, c_0_13])).
% 0.19/0.39  cnf(c_0_25, negated_conjecture, (v2_tex_2(u1_struct_0(esk5_0),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (v3_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_28, plain, (v3_tex_2(esk3_2(X1,u1_struct_0(X2)),X1)|v2_struct_0(X1)|~v3_tdlat_3(X1)|~v2_tex_2(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_13])).
% 0.19/0.39  fof(c_0_29, plain, ![X13, X14]:((((~v2_struct_0(esk2_2(X13,X14))|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13))))|(v2_struct_0(X13)|~l1_pre_topc(X13)))&(v1_pre_topc(esk2_2(X13,X14))|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13))))|(v2_struct_0(X13)|~l1_pre_topc(X13))))&(m1_pre_topc(esk2_2(X13,X14),X13)|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13))))|(v2_struct_0(X13)|~l1_pre_topc(X13))))&(X14=u1_struct_0(esk2_2(X13,X14))|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13))))|(v2_struct_0(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.19/0.39  cnf(c_0_30, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk3_2(esk4_0,u1_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_17]), c_0_19])]), c_0_21])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (v3_tex_2(esk3_2(esk4_0,u1_struct_0(esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26]), c_0_27]), c_0_17]), c_0_19])]), c_0_21])).
% 0.19/0.39  fof(c_0_33, plain, ![X9, X10, X11]:((~v4_tex_2(X10,X9)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|(X11!=u1_struct_0(X10)|v3_tex_2(X11,X9)))|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~l1_pre_topc(X9)))&((m1_subset_1(esk1_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))|v4_tex_2(X10,X9)|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~l1_pre_topc(X9)))&((esk1_2(X9,X10)=u1_struct_0(X10)|v4_tex_2(X10,X9)|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~l1_pre_topc(X9)))&(~v3_tex_2(esk1_2(X9,X10),X9)|v4_tex_2(X10,X9)|~m1_pre_topc(X10,X9)|(v2_struct_0(X9)|~l1_pre_topc(X9)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tex_2])])])])])])).
% 0.19/0.39  cnf(c_0_34, plain, (m1_pre_topc(esk2_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (~v1_xboole_0(esk3_2(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_27]), c_0_19])]), c_0_21])).
% 0.19/0.39  cnf(c_0_36, plain, (X1=u1_struct_0(esk2_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_37, plain, (v1_pre_topc(esk2_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_38, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk2_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  cnf(c_0_39, plain, (esk1_2(X1,X2)=u1_struct_0(X2)|v4_tex_2(X2,X1)|v2_struct_0(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_31]), c_0_19])]), c_0_21]), c_0_35])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (u1_struct_0(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))=esk3_2(esk4_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_31]), c_0_19])]), c_0_21]), c_0_35])).
% 0.19/0.39  fof(c_0_42, plain, ![X6, X7, X8]:((~r1_tarski(u1_struct_0(X7),u1_struct_0(X8))|m1_pre_topc(X7,X8)|~m1_pre_topc(X8,X6)|~m1_pre_topc(X7,X6)|(~v2_pre_topc(X6)|~l1_pre_topc(X6)))&(~m1_pre_topc(X7,X8)|r1_tarski(u1_struct_0(X7),u1_struct_0(X8))|~m1_pre_topc(X8,X6)|~m1_pre_topc(X7,X6)|(~v2_pre_topc(X6)|~l1_pre_topc(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (v2_struct_0(X1)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(esk5_0,X1)|~v4_tex_2(X1,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (v1_pre_topc(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_19])]), c_0_21]), c_0_35])).
% 0.19/0.39  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_19])]), c_0_21]), c_0_35])).
% 0.19/0.39  cnf(c_0_46, plain, (v4_tex_2(X2,X1)|v2_struct_0(X1)|~v3_tex_2(esk1_2(X1,X2),X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (esk1_2(esk4_0,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))=esk3_2(esk4_0,u1_struct_0(esk5_0))|v4_tex_2(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_19])]), c_0_21]), c_0_41])).
% 0.19/0.39  cnf(c_0_48, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_49, plain, (r1_tarski(X1,esk3_2(X2,X1))|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v3_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (~v4_tex_2(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0)|~m1_pre_topc(esk5_0,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_40])])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (v4_tex_2(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32]), c_0_40]), c_0_19])]), c_0_21])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (m1_pre_topc(X1,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))|~r1_tarski(u1_struct_0(X1),esk3_2(esk4_0,u1_struct_0(esk5_0)))|~v2_pre_topc(X2)|~m1_pre_topc(esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_48, c_0_41])).
% 0.19/0.39  cnf(c_0_53, plain, (v2_struct_0(X1)|r1_tarski(u1_struct_0(X2),esk3_2(X1,u1_struct_0(X2)))|~v3_tdlat_3(X1)|~v2_tex_2(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_13])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (~m1_pre_topc(esk5_0,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (m1_pre_topc(X1,esk2_2(esk4_0,esk3_2(esk4_0,u1_struct_0(esk5_0))))|~r1_tarski(u1_struct_0(X1),esk3_2(esk4_0,u1_struct_0(esk5_0)))|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_40]), c_0_27]), c_0_19])])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (r1_tarski(u1_struct_0(esk5_0),esk3_2(esk4_0,u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_25]), c_0_26]), c_0_27]), c_0_17]), c_0_19])]), c_0_21])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_17])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 58
% 0.19/0.39  # Proof object clause steps            : 41
% 0.19/0.39  # Proof object formula steps           : 17
% 0.19/0.39  # Proof object conjectures             : 27
% 0.19/0.39  # Proof object clause conjectures      : 24
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 21
% 0.19/0.39  # Proof object initial formulas used   : 8
% 0.19/0.39  # Proof object generating inferences   : 18
% 0.19/0.39  # Proof object simplifying inferences  : 66
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 8
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 25
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 25
% 0.19/0.39  # Processed clauses                    : 262
% 0.19/0.39  # ...of these trivial                  : 3
% 0.19/0.39  # ...subsumed                          : 51
% 0.19/0.39  # ...remaining for further processing  : 208
% 0.19/0.39  # Other redundant clauses eliminated   : 3
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 32
% 0.19/0.39  # Backward-rewritten                   : 4
% 0.19/0.39  # Generated clauses                    : 423
% 0.19/0.39  # ...of the previous two non-trivial   : 412
% 0.19/0.39  # Contextual simplify-reflections      : 41
% 0.19/0.39  # Paramodulations                      : 420
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 3
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 144
% 0.19/0.39  #    Positive orientable unit clauses  : 13
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 5
% 0.19/0.39  #    Non-unit-clauses                  : 126
% 0.19/0.39  # Current number of unprocessed clauses: 177
% 0.19/0.39  # ...number of literals in the above   : 969
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 61
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 3657
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 966
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 111
% 0.19/0.39  # Unit Clause-clause subsumption calls : 156
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 9
% 0.19/0.39  # BW rewrite match successes           : 8
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 16579
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.051 s
% 0.19/0.40  # System time              : 0.005 s
% 0.19/0.40  # Total time               : 0.056 s
% 0.19/0.40  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
