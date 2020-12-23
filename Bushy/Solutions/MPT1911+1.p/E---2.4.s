%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tex_2__t79_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:57 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  52 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :  201 ( 577 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v3_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v1_tdlat_3(X2)
            & m1_pre_topc(X2,X1) )
         => r1_borsuk_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t79_tex_2)).

fof(d20_borsuk_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( r1_borsuk_1(X1,X2)
          <=> ? [X3] :
                ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & v5_pre_topc(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                & v3_borsuk_1(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',d20_borsuk_1)).

fof(t78_tex_2,axiom,(
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
              ( v1_funct_1(X3)
              & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
              & v5_pre_topc(X3,X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
              & v3_borsuk_1(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t79_tex_2.p',t78_tex_2)).

fof(c_0_3,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v3_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v1_tdlat_3(X2)
              & m1_pre_topc(X2,X1) )
           => r1_borsuk_1(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t79_tex_2])).

fof(c_0_4,plain,(
    ! [X13,X14,X16] :
      ( ( v1_funct_1(esk3_2(X13,X14))
        | ~ r1_borsuk_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v1_funct_2(esk3_2(X13,X14),u1_struct_0(X13),u1_struct_0(X14))
        | ~ r1_borsuk_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v5_pre_topc(esk3_2(X13,X14),X13,X14)
        | ~ r1_borsuk_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_2(X13,X14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ r1_borsuk_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( v3_borsuk_1(esk3_2(X13,X14),X13,X14)
        | ~ r1_borsuk_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) )
      & ( ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,u1_struct_0(X13),u1_struct_0(X14))
        | ~ v5_pre_topc(X16,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ v3_borsuk_1(X16,X13,X14)
        | r1_borsuk_1(X13,X14)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | v2_struct_0(X13)
        | ~ v2_pre_topc(X13)
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d20_borsuk_1])])])])])])).

fof(c_0_5,plain,(
    ! [X41,X42] :
      ( ( v1_funct_1(esk9_2(X41,X42))
        | v2_struct_0(X42)
        | ~ v1_tdlat_3(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ v3_tdlat_3(X41)
        | ~ l1_pre_topc(X41) )
      & ( v1_funct_2(esk9_2(X41,X42),u1_struct_0(X41),u1_struct_0(X42))
        | v2_struct_0(X42)
        | ~ v1_tdlat_3(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ v3_tdlat_3(X41)
        | ~ l1_pre_topc(X41) )
      & ( v5_pre_topc(esk9_2(X41,X42),X41,X42)
        | v2_struct_0(X42)
        | ~ v1_tdlat_3(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ v3_tdlat_3(X41)
        | ~ l1_pre_topc(X41) )
      & ( m1_subset_1(esk9_2(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X42))))
        | v2_struct_0(X42)
        | ~ v1_tdlat_3(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ v3_tdlat_3(X41)
        | ~ l1_pre_topc(X41) )
      & ( v3_borsuk_1(esk9_2(X41,X42),X41,X42)
        | v2_struct_0(X42)
        | ~ v1_tdlat_3(X42)
        | ~ m1_pre_topc(X42,X41)
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ v3_tdlat_3(X41)
        | ~ l1_pre_topc(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tex_2])])])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & v3_tdlat_3(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v1_tdlat_3(esk2_0)
    & m1_pre_topc(esk2_0,esk1_0)
    & ~ r1_borsuk_1(esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])).

cnf(c_0_7,plain,
    ( r1_borsuk_1(X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v3_borsuk_1(X1,X2,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_8,plain,
    ( m1_subset_1(esk9_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( v1_funct_1(esk9_2(X1,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,plain,
    ( v1_funct_2(esk9_2(X1,X2),u1_struct_0(X1),u1_struct_0(X2))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,plain,
    ( v5_pre_topc(esk9_2(X1,X2),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( v3_borsuk_1(esk9_2(X1,X2),X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( ~ r1_borsuk_1(esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,plain,
    ( r1_borsuk_1(X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_tdlat_3(X2)
    | ~ l1_pre_topc(X1)
    | ~ v3_tdlat_3(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_7,c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,negated_conjecture,
    ( v1_tdlat_3(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( v3_tdlat_3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
