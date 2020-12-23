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
% DateTime   : Thu Dec  3 11:20:17 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 231 expanded)
%              Number of clauses        :   41 (  94 expanded)
%              Number of leaves         :   10 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  363 (1787 expanded)
%              Number of equality atoms :    8 (  64 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(cc25_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v7_struct_0(X2)
              & v2_pre_topc(X2) )
           => ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2)
              & v2_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc25_tex_2)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc6_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v7_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(cc32_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & ~ v7_struct_0(X2) )
           => ( ~ v2_struct_0(X2)
              & ~ v1_tdlat_3(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

fof(t44_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(fc7_struct_0,axiom,(
    ! [X1] :
      ( ( v7_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_zfmisc_1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(c_0_10,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_tex_2(X20,X18)
        | v1_tdlat_3(X19)
        | X20 != u1_struct_0(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ v1_tdlat_3(X19)
        | v2_tex_2(X20,X18)
        | X20 != u1_struct_0(X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).

cnf(c_0_11,plain,
    ( v2_tex_2(X2,X3)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v1_tdlat_3(X1)
    | X2 != u1_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ( ~ v2_struct_0(esk1_2(X15,X16))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) )
      & ( v1_pre_topc(esk1_2(X15,X16))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_pre_topc(esk1_2(X15,X16),X15)
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) )
      & ( X16 = u1_struct_0(esk1_2(X15,X16))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( ~ v2_struct_0(X12)
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) )
      & ( v1_tdlat_3(X12)
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) )
      & ( v2_tdlat_3(X12)
        | v2_struct_0(X12)
        | ~ v7_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ m1_pre_topc(X12,X11)
        | v2_struct_0(X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc25_tex_2])])])])])).

fof(c_0_14,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(X4)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X5,X4)
      | v2_pre_topc(X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X7,X8] :
      ( ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | l1_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_16,plain,
    ( v2_tex_2(u1_struct_0(X1),X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( X1 = u1_struct_0(esk1_2(X2,X1))
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v2_struct_0(esk1_2(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v7_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( m1_pre_topc(esk1_2(X1,X2),X1)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_22,plain,(
    ! [X6] :
      ( ~ l1_pre_topc(X6)
      | l1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_tdlat_3(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | X1 != u1_struct_0(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( v2_tex_2(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v1_tdlat_3(esk1_2(X3,X1))
    | ~ m1_pre_topc(esk1_2(X3,X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])).

cnf(c_0_26,plain,
    ( v1_xboole_0(X1)
    | v1_tdlat_3(esk1_2(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(esk1_2(X2,X1))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(esk1_2(X2,X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_18])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | v2_pre_topc(esk1_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

fof(c_0_28,plain,(
    ! [X9] :
      ( v7_struct_0(X9)
      | ~ l1_struct_0(X9)
      | ~ v1_zfmisc_1(u1_struct_0(X9)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).

cnf(c_0_29,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | l1_pre_topc(esk1_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

fof(c_0_31,plain,(
    ! [X13,X14] :
      ( ( ~ v2_struct_0(X14)
        | v2_struct_0(X14)
        | v7_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v2_tdlat_3(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ v1_tdlat_3(X14)
        | v2_struct_0(X14)
        | v7_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ v2_tdlat_3(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).

cnf(c_0_32,plain,
    ( v1_tdlat_3(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_tex_2(u1_struct_0(X1),X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_24])).

fof(c_0_33,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

cnf(c_0_34,plain,
    ( v2_tex_2(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_tdlat_3(esk1_2(X2,X1))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_20])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X1)
    | v1_tdlat_3(esk1_2(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(esk1_2(X2,X1))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( v7_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_zfmisc_1(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | l1_struct_0(esk1_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_38,plain,(
    ! [X10] :
      ( ~ v7_struct_0(X10)
      | ~ l1_struct_0(X10)
      | v1_zfmisc_1(u1_struct_0(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | v7_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_tdlat_3(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X1)
    | v1_tdlat_3(esk1_2(X2,X1))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_tex_2(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk1_2(X2,X1),X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_17]),c_0_18])).

fof(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & v2_tdlat_3(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v1_xboole_0(esk3_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v2_tex_2(esk3_0,esk2_0)
      | ~ v1_zfmisc_1(esk3_0) )
    & ( v2_tex_2(esk3_0,esk2_0)
      | v1_zfmisc_1(esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).

cnf(c_0_42,plain,
    ( v2_tex_2(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(esk1_2(X2,X1))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | v7_struct_0(esk1_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_zfmisc_1(X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_17]),c_0_37])).

cnf(c_0_44,plain,
    ( v1_zfmisc_1(u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | v7_struct_0(esk1_2(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tdlat_3(X2)
    | ~ v1_tdlat_3(esk1_2(X2,X1))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_20]),c_0_18])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | v1_tdlat_3(esk1_2(X2,X1))
    | v2_struct_0(X2)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_tex_2(esk3_0,esk2_0)
    | ~ v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_48,plain,
    ( v2_tex_2(X1,X2)
    | v1_xboole_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_zfmisc_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | v1_zfmisc_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v7_struct_0(esk1_2(X2,X1))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_17]),c_0_37])).

cnf(c_0_55,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | v7_struct_0(esk1_2(X2,X1))
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( v2_tex_2(esk3_0,esk2_0)
    | v1_zfmisc_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_zfmisc_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])]),c_0_52]),c_0_53])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | v2_struct_0(X2)
    | v1_zfmisc_1(X1)
    | ~ v2_tex_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_tdlat_3(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_59,negated_conjecture,
    ( v2_tex_2(esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( v2_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_49]),c_0_60]),c_0_50]),c_0_51])]),c_0_52]),c_0_53]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.14/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t26_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>(v2_tex_2(X3,X1)<=>v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 0.14/0.38  fof(t10_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>?[X3]:(((~(v2_struct_0(X3))&v1_pre_topc(X3))&m1_pre_topc(X3,X1))&X2=u1_struct_0(X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 0.14/0.38  fof(cc25_tex_2, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>(((~(v2_struct_0(X2))&v7_struct_0(X2))&v2_pre_topc(X2))=>((~(v2_struct_0(X2))&v1_tdlat_3(X2))&v2_tdlat_3(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc25_tex_2)).
% 0.14/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.14/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.14/0.38  fof(fc6_struct_0, axiom, ![X1]:((~(v7_struct_0(X1))&l1_struct_0(X1))=>~(v1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 0.14/0.38  fof(cc32_tex_2, axiom, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>((~(v2_struct_0(X2))&~(v7_struct_0(X2)))=>(~(v2_struct_0(X2))&~(v1_tdlat_3(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 0.14/0.38  fof(t44_tex_2, conjecture, ![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 0.14/0.38  fof(fc7_struct_0, axiom, ![X1]:((v7_struct_0(X1)&l1_struct_0(X1))=>v1_zfmisc_1(u1_struct_0(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 0.14/0.38  fof(c_0_10, plain, ![X18, X19, X20]:((~v2_tex_2(X20,X18)|v1_tdlat_3(X19)|X20!=u1_struct_0(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~l1_pre_topc(X18)))&(~v1_tdlat_3(X19)|v2_tex_2(X20,X18)|X20!=u1_struct_0(X19)|~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))|(v2_struct_0(X19)|~m1_pre_topc(X19,X18))|(v2_struct_0(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t26_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_11, plain, (v2_tex_2(X2,X3)|v2_struct_0(X1)|v2_struct_0(X3)|~v1_tdlat_3(X1)|X2!=u1_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  fof(c_0_12, plain, ![X15, X16]:((((~v2_struct_0(esk1_2(X15,X16))|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))))|(v2_struct_0(X15)|~l1_pre_topc(X15)))&(v1_pre_topc(esk1_2(X15,X16))|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))))|(v2_struct_0(X15)|~l1_pre_topc(X15))))&(m1_pre_topc(esk1_2(X15,X16),X15)|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))))|(v2_struct_0(X15)|~l1_pre_topc(X15))))&(X16=u1_struct_0(esk1_2(X15,X16))|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15))))|(v2_struct_0(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_tsep_1])])])])])])).
% 0.14/0.38  fof(c_0_13, plain, ![X11, X12]:(((~v2_struct_0(X12)|(v2_struct_0(X12)|~v7_struct_0(X12)|~v2_pre_topc(X12))|~m1_pre_topc(X12,X11)|(v2_struct_0(X11)|~l1_pre_topc(X11)))&(v1_tdlat_3(X12)|(v2_struct_0(X12)|~v7_struct_0(X12)|~v2_pre_topc(X12))|~m1_pre_topc(X12,X11)|(v2_struct_0(X11)|~l1_pre_topc(X11))))&(v2_tdlat_3(X12)|(v2_struct_0(X12)|~v7_struct_0(X12)|~v2_pre_topc(X12))|~m1_pre_topc(X12,X11)|(v2_struct_0(X11)|~l1_pre_topc(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc25_tex_2])])])])])).
% 0.14/0.38  fof(c_0_14, plain, ![X4, X5]:(~v2_pre_topc(X4)|~l1_pre_topc(X4)|(~m1_pre_topc(X5,X4)|v2_pre_topc(X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.14/0.38  fof(c_0_15, plain, ![X7, X8]:(~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|l1_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.38  cnf(c_0_16, plain, (v2_tex_2(u1_struct_0(X1),X2)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(er,[status(thm)],[c_0_11])).
% 0.14/0.38  cnf(c_0_17, plain, (X1=u1_struct_0(esk1_2(X2,X1))|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, plain, (v1_xboole_0(X2)|v2_struct_0(X1)|~v2_struct_0(esk1_2(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_19, plain, (v1_tdlat_3(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v7_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.38  cnf(c_0_20, plain, (m1_pre_topc(esk1_2(X1,X2),X1)|v1_xboole_0(X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_21, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.38  fof(c_0_22, plain, ![X6]:(~l1_pre_topc(X6)|l1_struct_0(X6)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.14/0.38  cnf(c_0_23, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_24, plain, (v1_tdlat_3(X3)|v2_struct_0(X3)|v2_struct_0(X2)|~v2_tex_2(X1,X2)|X1!=u1_struct_0(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_25, plain, (v2_tex_2(X1,X2)|v1_xboole_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))|~v1_tdlat_3(esk1_2(X3,X1))|~m1_pre_topc(esk1_2(X3,X1),X2)|~l1_pre_topc(X2)|~l1_pre_topc(X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])).
% 0.14/0.38  cnf(c_0_26, plain, (v1_xboole_0(X1)|v1_tdlat_3(esk1_2(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(esk1_2(X2,X1))|~l1_pre_topc(X2)|~v2_pre_topc(esk1_2(X2,X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_18])).
% 0.14/0.38  cnf(c_0_27, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|v2_pre_topc(esk1_2(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.14/0.38  fof(c_0_28, plain, ![X9]:(v7_struct_0(X9)|~l1_struct_0(X9)|~v1_zfmisc_1(u1_struct_0(X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc6_struct_0])])])).
% 0.14/0.38  cnf(c_0_29, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  cnf(c_0_30, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|l1_pre_topc(esk1_2(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_23, c_0_20])).
% 0.14/0.38  fof(c_0_31, plain, ![X13, X14]:((~v2_struct_0(X14)|(v2_struct_0(X14)|v7_struct_0(X14))|~m1_pre_topc(X14,X13)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v2_tdlat_3(X13)|~l1_pre_topc(X13)))&(~v1_tdlat_3(X14)|(v2_struct_0(X14)|v7_struct_0(X14))|~m1_pre_topc(X14,X13)|(v2_struct_0(X13)|~v2_pre_topc(X13)|~v2_tdlat_3(X13)|~l1_pre_topc(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc32_tex_2])])])])])).
% 0.14/0.38  cnf(c_0_32, plain, (v1_tdlat_3(X1)|v2_struct_0(X1)|v2_struct_0(X2)|~v2_tex_2(u1_struct_0(X1),X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(er,[status(thm)],[c_0_24])).
% 0.14/0.38  fof(c_0_33, negated_conjecture, ~(![X1]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&v2_tdlat_3(X1))&l1_pre_topc(X1))=>![X2]:((~(v1_xboole_0(X2))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tex_2(X2,X1)<=>v1_zfmisc_1(X2))))), inference(assume_negation,[status(cth)],[t44_tex_2])).
% 0.14/0.38  cnf(c_0_34, plain, (v2_tex_2(X1,X2)|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v1_tdlat_3(esk1_2(X2,X1))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_25, c_0_20])).
% 0.14/0.38  cnf(c_0_35, plain, (v1_xboole_0(X1)|v1_tdlat_3(esk1_2(X2,X1))|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(esk1_2(X2,X1))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_36, plain, (v7_struct_0(X1)|~l1_struct_0(X1)|~v1_zfmisc_1(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.38  cnf(c_0_37, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|l1_struct_0(esk1_2(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.38  fof(c_0_38, plain, ![X10]:(~v7_struct_0(X10)|~l1_struct_0(X10)|v1_zfmisc_1(u1_struct_0(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc7_struct_0])])).
% 0.14/0.38  cnf(c_0_39, plain, (v2_struct_0(X1)|v7_struct_0(X1)|v2_struct_0(X2)|~v1_tdlat_3(X1)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~v2_tdlat_3(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.38  cnf(c_0_40, plain, (v1_xboole_0(X1)|v1_tdlat_3(esk1_2(X2,X1))|v2_struct_0(X2)|v2_struct_0(X3)|~v2_tex_2(X1,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(esk1_2(X2,X1),X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_17]), c_0_18])).
% 0.14/0.38  fof(c_0_41, negated_conjecture, ((((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&v2_tdlat_3(esk2_0))&l1_pre_topc(esk2_0))&((~v1_xboole_0(esk3_0)&m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))))&((~v2_tex_2(esk3_0,esk2_0)|~v1_zfmisc_1(esk3_0))&(v2_tex_2(esk3_0,esk2_0)|v1_zfmisc_1(esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_33])])])])).
% 0.14/0.38  cnf(c_0_42, plain, (v2_tex_2(X1,X2)|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(esk1_2(X2,X1))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.14/0.38  cnf(c_0_43, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|v7_struct_0(esk1_2(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v1_zfmisc_1(X1)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_17]), c_0_37])).
% 0.14/0.38  cnf(c_0_44, plain, (v1_zfmisc_1(u1_struct_0(X1))|~v7_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_45, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|v7_struct_0(esk1_2(X2,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tdlat_3(X2)|~v1_tdlat_3(esk1_2(X2,X1))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_20]), c_0_18])).
% 0.14/0.38  cnf(c_0_46, plain, (v1_xboole_0(X1)|v1_tdlat_3(esk1_2(X2,X1))|v2_struct_0(X2)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_40, c_0_20])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (~v2_tex_2(esk3_0,esk2_0)|~v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_48, plain, (v2_tex_2(X1,X2)|v1_xboole_0(X1)|v2_struct_0(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v1_zfmisc_1(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (~v1_xboole_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_54, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|v1_zfmisc_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v7_struct_0(esk1_2(X2,X1))|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_17]), c_0_37])).
% 0.14/0.38  cnf(c_0_55, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|v7_struct_0(esk1_2(X2,X1))|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tdlat_3(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (v2_tex_2(esk3_0,esk2_0)|v1_zfmisc_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (~v1_zfmisc_1(esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])]), c_0_52]), c_0_53])).
% 0.14/0.38  cnf(c_0_58, plain, (v1_xboole_0(X1)|v2_struct_0(X2)|v1_zfmisc_1(X1)|~v2_tex_2(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_tdlat_3(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (v2_tex_2(esk3_0,esk2_0)), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (v2_tdlat_3(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_49]), c_0_60]), c_0_50]), c_0_51])]), c_0_52]), c_0_53]), c_0_57]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 62
% 0.14/0.38  # Proof object clause steps            : 41
% 0.14/0.38  # Proof object formula steps           : 21
% 0.14/0.38  # Proof object conjectures             : 14
% 0.14/0.38  # Proof object clause conjectures      : 11
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 20
% 0.14/0.38  # Proof object initial formulas used   : 10
% 0.14/0.38  # Proof object generating inferences   : 18
% 0.14/0.38  # Proof object simplifying inferences  : 23
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 24
% 0.14/0.38  # Removed in clause preprocessing      : 2
% 0.14/0.38  # Initial clauses in saturation        : 22
% 0.14/0.38  # Processed clauses                    : 70
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 2
% 0.14/0.38  # ...remaining for further processing  : 68
% 0.14/0.38  # Other redundant clauses eliminated   : 2
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 1
% 0.14/0.38  # Generated clauses                    : 37
% 0.14/0.38  # ...of the previous two non-trivial   : 28
% 0.14/0.38  # Contextual simplify-reflections      : 8
% 0.14/0.38  # Paramodulations                      : 34
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 2
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 42
% 0.14/0.38  #    Positive orientable unit clauses  : 6
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 3
% 0.14/0.38  #    Non-unit-clauses                  : 33
% 0.14/0.38  # Current number of unprocessed clauses: 2
% 0.14/0.38  # ...number of literals in the above   : 28
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 24
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 1019
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 39
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 8
% 0.14/0.38  # Unit Clause-clause subsumption calls : 15
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 1
% 0.14/0.38  # BW rewrite match successes           : 1
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3779
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.035 s
% 0.14/0.38  # System time              : 0.001 s
% 0.14/0.38  # Total time               : 0.036 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
