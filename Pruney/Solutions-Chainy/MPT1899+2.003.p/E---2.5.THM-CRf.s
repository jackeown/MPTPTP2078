%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:20:59 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 871 expanded)
%              Number of clauses        :   42 ( 285 expanded)
%              Number of leaves         :    7 ( 217 expanded)
%              Depth                    :   10
%              Number of atoms          :  341 (7458 expanded)
%              Number of equality atoms :    9 (  67 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   35 (   4 average)
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

fof(t53_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ~ ( v3_tex_2(X2,X1)
              & ! [X3] :
                  ( ( ~ v2_struct_0(X3)
                    & v1_pre_topc(X3)
                    & m1_pre_topc(X3,X1) )
                 => ~ ( v4_tex_2(X3,X1)
                      & X2 = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

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

fof(c_0_7,plain,(
    ! [X9,X10,X11] :
      ( ( ~ v2_tex_2(X11,X9)
        | v1_tdlat_3(X10)
        | X11 != u1_struct_0(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ v1_tdlat_3(X10)
        | v2_tex_2(X11,X9)
        | X11 != u1_struct_0(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,X9)
        | v2_struct_0(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X5,X4)
      | m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X17,X18] :
      ( ( m1_subset_1(esk2_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) )
      & ( r1_tarski(X18,esk2_2(X17,X18))
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) )
      & ( v3_tex_2(esk2_2(X17,X18),X17)
        | ~ v2_tex_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ v3_tdlat_3(X17)
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).

cnf(c_0_11,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,negated_conjecture,(
    ! [X22] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & v3_tdlat_3(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & v1_tdlat_3(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ( v2_struct_0(X22)
        | ~ v1_pre_topc(X22)
        | ~ m1_pre_topc(X22,esk3_0)
        | ~ m1_pre_topc(esk4_0,X22)
        | ~ v4_tex_2(X22,esk3_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_14,plain,(
    ! [X14,X15] :
      ( ( ~ v2_struct_0(esk1_2(X14,X15))
        | ~ v3_tex_2(X15,X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( v1_pre_topc(esk1_2(X14,X15))
        | ~ v3_tex_2(X15,X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( m1_pre_topc(esk1_2(X14,X15),X14)
        | ~ v3_tex_2(X15,X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( v4_tex_2(esk1_2(X14,X15),X14)
        | ~ v3_tex_2(X15,X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( X15 = u1_struct_0(esk1_2(X14,X15))
        | ~ v3_tex_2(X15,X14)
        | v1_xboole_0(X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t53_tex_2])])])])])])).

fof(c_0_15,plain,(
    ! [X12,X13] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v1_xboole_0(X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ v3_tex_2(X13,X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]),c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v1_tdlat_3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v3_tex_2(esk2_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
    ( X1 = u1_struct_0(esk1_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ v3_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,plain,
    ( v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tex_2(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk2_2(X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_tex_2(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v2_tex_2(u1_struct_0(esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21]),c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( v3_tdlat_3(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( v3_tex_2(esk2_2(X1,u1_struct_0(X2)),X1)
    | v2_struct_0(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_tex_2(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_31,plain,
    ( v4_tex_2(esk1_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( v1_pre_topc(esk1_2(X1,X2))
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,plain,
    ( m1_pre_topc(esk1_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_34,plain,(
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

cnf(c_0_35,plain,
    ( u1_struct_0(esk1_2(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_2(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( v3_tex_2(esk2_2(esk3_0,u1_struct_0(esk4_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_28]),c_0_29]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_38,plain,
    ( v4_tex_2(esk1_2(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_39,plain,
    ( v1_pre_topc(esk1_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | m1_pre_topc(esk1_2(X1,X2),X1)
    | ~ v3_tex_2(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_33,c_0_25])).

cnf(c_0_41,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( u1_struct_0(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0)))) = esk2_2(esk3_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_29]),c_0_20])]),c_0_22])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,esk2_2(X2,X1))
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ v3_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( v2_struct_0(X1)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ v4_tex_2(X1,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v4_tex_2(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_36]),c_0_37]),c_0_29]),c_0_20])]),c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( v1_pre_topc(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_36]),c_0_37]),c_0_29]),c_0_20])]),c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_36]),c_0_37]),c_0_29]),c_0_20])]),c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(X1,esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))
    | ~ r1_tarski(u1_struct_0(X1),esk2_2(esk3_0,u1_struct_0(esk4_0)))
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( v2_struct_0(X1)
    | r1_tarski(u1_struct_0(X2),esk2_2(X1,u1_struct_0(X2)))
    | ~ v3_tdlat_3(X1)
    | ~ v2_tex_2(u1_struct_0(X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_12])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1_2(X1,X2))
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_51,negated_conjecture,
    ( v2_struct_0(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))
    | ~ m1_pre_topc(esk4_0,esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(X1,esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))
    | ~ r1_tarski(u1_struct_0(X1),esk2_2(esk3_0,u1_struct_0(esk4_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_29]),c_0_20])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk4_0),esk2_2(esk3_0,u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_28]),c_0_29]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | ~ v3_tex_2(X2,X1)
    | ~ v2_struct_0(esk1_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_50,c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( v2_struct_0(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53]),c_0_18])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_37]),c_0_29]),c_0_36]),c_0_20])]),c_0_22]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.38  #
% 0.20/0.38  # Preprocessing time       : 0.029 s
% 0.20/0.38  # Presaturation interreduction done
% 0.20/0.38  
% 0.20/0.38  # Proof found!
% 0.20/0.38  # SZS status Theorem
% 0.20/0.38  # SZS output start CNFRefutation
% 0.20/0.38  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 0.20/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.38  fof(t67_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>?[X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&m1_pre_topc(X2,X3))&v4_tex_2(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tex_2)).
% 0.20/0.38  fof(t65_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>~((v2_tex_2(X2,X1)&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X2,X3)&v3_tex_2(X3,X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tex_2)).
% 0.20/0.38  fof(t53_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~((v3_tex_2(X2,X1)&![X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))=>~((v4_tex_2(X3,X1)&X2=u1_struct_0(X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 0.20/0.38  fof(t46_tex_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((v1_xboole_0(X2)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>~(v3_tex_2(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_tex_2)).
% 0.20/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.38  fof(c_0_7, plain, ![X9, X10, X11]:((~v2_tex_2(X11,X9)|v1_tdlat_3(X10)|X11!=u1_struct_0(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X10)|~m1_pre_topc(X10,X9))|(v2_struct_0(X9)|~l1_pre_topc(X9)))&(~v1_tdlat_3(X10)|v2_tex_2(X11,X9)|X11!=u1_struct_0(X10)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|(v2_struct_0(X10)|~m1_pre_topc(X10,X9))|(v2_struct_0(X9)|~l1_pre_topc(X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.20/0.38  fof(c_0_8, plain, ![X4, X5]:(~l1_pre_topc(X4)|(~m1_pre_topc(X5,X4)|m1_subset_1(u1_struct_0(X5),k1_zfmisc_1(u1_struct_0(X4))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.38  fof(c_0_9, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v3_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v1_tdlat_3(X2))&m1_pre_topc(X2,X1))=>?[X3]:((((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&m1_pre_topc(X2,X3))&v4_tex_2(X3,X1))))), inference(assume_negation,[status(cth)],[t67_tex_2])).
% 0.20/0.38  fof(c_0_10, plain, ![X17, X18]:((m1_subset_1(esk2_2(X17,X18),k1_zfmisc_1(u1_struct_0(X17)))|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17)))&((r1_tarski(X18,esk2_2(X17,X18))|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17)))&(v3_tex_2(esk2_2(X17,X18),X17)|~v2_tex_2(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~v3_tdlat_3(X17)|~l1_pre_topc(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tex_2])])])])])])).
% 0.20/0.38  cnf(c_0_11, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.38  cnf(c_0_12, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.38  fof(c_0_13, negated_conjecture, ![X22]:((((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&v3_tdlat_3(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v1_tdlat_3(esk4_0))&m1_pre_topc(esk4_0,esk3_0))&(v2_struct_0(X22)|~v1_pre_topc(X22)|~m1_pre_topc(X22,esk3_0)|~m1_pre_topc(esk4_0,X22)|~v4_tex_2(X22,esk3_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.20/0.38  fof(c_0_14, plain, ![X14, X15]:((((~v2_struct_0(esk1_2(X14,X15))|~v3_tex_2(X15,X14)|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(v1_pre_topc(esk1_2(X14,X15))|~v3_tex_2(X15,X14)|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))&(m1_pre_topc(esk1_2(X14,X15),X14)|~v3_tex_2(X15,X14)|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))&((v4_tex_2(esk1_2(X14,X15),X14)|~v3_tex_2(X15,X14)|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(X15=u1_struct_0(esk1_2(X14,X15))|~v3_tex_2(X15,X14)|(v1_xboole_0(X15)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14))))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t53_tex_2])])])])])])).
% 0.20/0.38  fof(c_0_15, plain, ![X12, X13]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~v1_xboole_0(X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~v3_tex_2(X13,X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t46_tex_2])])])])).
% 0.20/0.38  cnf(c_0_16, plain, (m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_17, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_11]), c_0_12])).
% 0.20/0.38  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_19, negated_conjecture, (v1_tdlat_3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_23, plain, (v3_tex_2(esk2_2(X1,X2),X1)|v2_struct_0(X1)|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~v3_tdlat_3(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_24, plain, (X1=u1_struct_0(esk1_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~v3_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_25, plain, (v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v3_tex_2(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.38  cnf(c_0_26, plain, (v2_struct_0(X1)|m1_subset_1(esk2_2(X1,u1_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X1)))|~v3_tdlat_3(X1)|~v2_tex_2(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_16, c_0_12])).
% 0.20/0.38  cnf(c_0_27, negated_conjecture, (v2_tex_2(u1_struct_0(esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21]), c_0_22])).
% 0.20/0.38  cnf(c_0_28, negated_conjecture, (v3_tdlat_3(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_30, plain, (v3_tex_2(esk2_2(X1,u1_struct_0(X2)),X1)|v2_struct_0(X1)|~v3_tdlat_3(X1)|~v2_tex_2(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_12])).
% 0.20/0.38  cnf(c_0_31, plain, (v4_tex_2(esk1_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v3_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_32, plain, (v1_pre_topc(esk1_2(X1,X2))|v1_xboole_0(X2)|v2_struct_0(X1)|~v3_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_33, plain, (m1_pre_topc(esk1_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~v3_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  fof(c_0_34, plain, ![X6, X7, X8]:((~r1_tarski(u1_struct_0(X7),u1_struct_0(X8))|m1_pre_topc(X7,X8)|~m1_pre_topc(X8,X6)|~m1_pre_topc(X7,X6)|(~v2_pre_topc(X6)|~l1_pre_topc(X6)))&(~m1_pre_topc(X7,X8)|r1_tarski(u1_struct_0(X7),u1_struct_0(X8))|~m1_pre_topc(X8,X6)|~m1_pre_topc(X7,X6)|(~v2_pre_topc(X6)|~l1_pre_topc(X6)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.38  cnf(c_0_35, plain, (u1_struct_0(esk1_2(X1,X2))=X2|v2_struct_0(X1)|~v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk2_2(esk3_0,u1_struct_0(esk4_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_18]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_37, negated_conjecture, (v3_tex_2(esk2_2(esk3_0,u1_struct_0(esk4_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_28]), c_0_29]), c_0_18]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_38, plain, (v4_tex_2(esk1_2(X1,X2),X1)|v2_struct_0(X1)|~v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_31, c_0_25])).
% 0.20/0.38  cnf(c_0_39, plain, (v1_pre_topc(esk1_2(X1,X2))|v2_struct_0(X1)|~v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_32, c_0_25])).
% 0.20/0.38  cnf(c_0_40, plain, (v2_struct_0(X1)|m1_pre_topc(esk1_2(X1,X2),X1)|~v3_tex_2(X2,X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_33, c_0_25])).
% 0.20/0.38  cnf(c_0_41, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.38  cnf(c_0_42, negated_conjecture, (u1_struct_0(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))=esk2_2(esk3_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_29]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_43, plain, (r1_tarski(X1,esk2_2(X2,X1))|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~v3_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.38  cnf(c_0_44, negated_conjecture, (v2_struct_0(X1)|~v1_pre_topc(X1)|~m1_pre_topc(X1,esk3_0)|~m1_pre_topc(esk4_0,X1)|~v4_tex_2(X1,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.38  cnf(c_0_45, negated_conjecture, (v4_tex_2(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_36]), c_0_37]), c_0_29]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_46, negated_conjecture, (v1_pre_topc(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_36]), c_0_37]), c_0_29]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_36]), c_0_37]), c_0_29]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_48, negated_conjecture, (m1_pre_topc(X1,esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))|~r1_tarski(u1_struct_0(X1),esk2_2(esk3_0,u1_struct_0(esk4_0)))|~v2_pre_topc(X2)|~m1_pre_topc(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.38  cnf(c_0_49, plain, (v2_struct_0(X1)|r1_tarski(u1_struct_0(X2),esk2_2(X1,u1_struct_0(X2)))|~v3_tdlat_3(X1)|~v2_tex_2(u1_struct_0(X2),X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_43, c_0_12])).
% 0.20/0.38  cnf(c_0_50, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk1_2(X1,X2))|~v3_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.38  cnf(c_0_51, negated_conjecture, (v2_struct_0(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))|~m1_pre_topc(esk4_0,esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.38  cnf(c_0_52, negated_conjecture, (m1_pre_topc(X1,esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))|~r1_tarski(u1_struct_0(X1),esk2_2(esk3_0,u1_struct_0(esk4_0)))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_47]), c_0_29]), c_0_20])])).
% 0.20/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(u1_struct_0(esk4_0),esk2_2(esk3_0,u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_28]), c_0_29]), c_0_18]), c_0_20])]), c_0_22])).
% 0.20/0.38  cnf(c_0_54, plain, (v2_struct_0(X1)|~v3_tex_2(X2,X1)|~v2_struct_0(esk1_2(X1,X2))|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[c_0_50, c_0_25])).
% 0.20/0.38  cnf(c_0_55, negated_conjecture, (v2_struct_0(esk1_2(esk3_0,esk2_2(esk3_0,u1_struct_0(esk4_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53]), c_0_18])])).
% 0.20/0.38  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_37]), c_0_29]), c_0_36]), c_0_20])]), c_0_22]), ['proof']).
% 0.20/0.38  # SZS output end CNFRefutation
% 0.20/0.38  # Proof object total steps             : 57
% 0.20/0.38  # Proof object clause steps            : 42
% 0.20/0.38  # Proof object formula steps           : 15
% 0.20/0.38  # Proof object conjectures             : 24
% 0.20/0.38  # Proof object clause conjectures      : 21
% 0.20/0.38  # Proof object formula conjectures     : 3
% 0.20/0.38  # Proof object initial clauses used    : 20
% 0.20/0.38  # Proof object initial formulas used   : 7
% 0.20/0.38  # Proof object generating inferences   : 16
% 0.20/0.38  # Proof object simplifying inferences  : 65
% 0.20/0.38  # Training examples: 0 positive, 0 negative
% 0.20/0.38  # Parsed axioms                        : 7
% 0.20/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.38  # Initial clauses                      : 22
% 0.20/0.38  # Removed in clause preprocessing      : 0
% 0.20/0.38  # Initial clauses in saturation        : 22
% 0.20/0.38  # Processed clauses                    : 85
% 0.20/0.38  # ...of these trivial                  : 0
% 0.20/0.38  # ...subsumed                          : 1
% 0.20/0.38  # ...remaining for further processing  : 84
% 0.20/0.38  # Other redundant clauses eliminated   : 2
% 0.20/0.38  # Clauses deleted for lack of memory   : 0
% 0.20/0.38  # Backward-subsumed                    : 0
% 0.20/0.38  # Backward-rewritten                   : 2
% 0.20/0.38  # Generated clauses                    : 77
% 0.20/0.38  # ...of the previous two non-trivial   : 68
% 0.20/0.38  # Contextual simplify-reflections      : 11
% 0.20/0.38  # Paramodulations                      : 75
% 0.20/0.38  # Factorizations                       : 0
% 0.20/0.38  # Equation resolutions                 : 2
% 0.20/0.38  # Propositional unsat checks           : 0
% 0.20/0.38  #    Propositional check models        : 0
% 0.20/0.38  #    Propositional check unsatisfiable : 0
% 0.20/0.38  #    Propositional clauses             : 0
% 0.20/0.38  #    Propositional clauses after purity: 0
% 0.20/0.38  #    Propositional unsat core size     : 0
% 0.20/0.38  #    Propositional preprocessing time  : 0.000
% 0.20/0.38  #    Propositional encoding time       : 0.000
% 0.20/0.38  #    Propositional solver time         : 0.000
% 0.20/0.38  #    Success case prop preproc time    : 0.000
% 0.20/0.38  #    Success case prop encoding time   : 0.000
% 0.20/0.38  #    Success case prop solver time     : 0.000
% 0.20/0.38  # Current number of processed clauses  : 58
% 0.20/0.38  #    Positive orientable unit clauses  : 14
% 0.20/0.38  #    Positive unorientable unit clauses: 0
% 0.20/0.38  #    Negative unit clauses             : 3
% 0.20/0.38  #    Non-unit-clauses                  : 41
% 0.20/0.38  # Current number of unprocessed clauses: 27
% 0.20/0.38  # ...number of literals in the above   : 151
% 0.20/0.38  # Current number of archived formulas  : 0
% 0.20/0.38  # Current number of archived clauses   : 24
% 0.20/0.38  # Clause-clause subsumption calls (NU) : 211
% 0.20/0.38  # Rec. Clause-clause subsumption calls : 42
% 0.20/0.38  # Non-unit clause-clause subsumptions  : 11
% 0.20/0.38  # Unit Clause-clause subsumption calls : 19
% 0.20/0.38  # Rewrite failures with RHS unbound    : 0
% 0.20/0.38  # BW rewrite match attempts            : 1
% 0.20/0.38  # BW rewrite match successes           : 1
% 0.20/0.38  # Condensation attempts                : 0
% 0.20/0.38  # Condensation successes               : 0
% 0.20/0.38  # Termbank termtop insertions          : 5564
% 0.20/0.38  
% 0.20/0.38  # -------------------------------------------------
% 0.20/0.38  # User time                : 0.034 s
% 0.20/0.38  # System time              : 0.004 s
% 0.20/0.38  # Total time               : 0.038 s
% 0.20/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
