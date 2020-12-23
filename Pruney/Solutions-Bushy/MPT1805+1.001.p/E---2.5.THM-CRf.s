%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1805+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   85 (1031 expanded)
%              Number of clauses        :   64 ( 339 expanded)
%              Number of leaves         :   10 ( 258 expanded)
%              Depth                    :   32
%              Number of atoms          :  487 (6819 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   34 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t121_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
            & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
            & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
            & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_tmap_1)).

fof(dt_k9_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k9_tmap_1(X1,X2))
        & v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
        & m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_tmap_1)).

fof(dt_k8_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2))
        & l1_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

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

fof(t119_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_tmap_1)).

fof(fc5_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( ~ v2_struct_0(k8_tmap_1(X1,X2))
        & v1_pre_topc(k8_tmap_1(X1,X2))
        & v2_pre_topc(k8_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_tmap_1)).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v5_pre_topc(X29,X28,X27)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | r1_tmap_1(X28,X27,X29,X30)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X28),u1_struct_0(X27))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( m1_subset_1(esk1_3(X27,X28,X29),u1_struct_0(X28))
        | v5_pre_topc(X29,X28,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X28),u1_struct_0(X27))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ r1_tmap_1(X28,X27,X29,esk1_3(X27,X28,X29))
        | v5_pre_topc(X29,X28,X27)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X28),u1_struct_0(X27))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | v2_struct_0(X27)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_11,plain,(
    ! [X10,X11,X12,X13] :
      ( ( v1_funct_1(k2_tmap_1(X10,X11,X12,X13))
        | ~ l1_struct_0(X10)
        | ~ l1_struct_0(X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_struct_0(X13) )
      & ( v1_funct_2(k2_tmap_1(X10,X11,X12,X13),u1_struct_0(X13),u1_struct_0(X11))
        | ~ l1_struct_0(X10)
        | ~ l1_struct_0(X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_struct_0(X13) )
      & ( m1_subset_1(k2_tmap_1(X10,X11,X12,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X11))))
        | ~ l1_struct_0(X10)
        | ~ l1_struct_0(X11)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
        | ~ l1_struct_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_12,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ( v1_funct_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2))
              & v1_funct_2(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2)))
              & v5_pre_topc(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X2,k8_tmap_1(X1,X2))
              & m1_subset_1(k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(k8_tmap_1(X1,X2))))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t121_tmap_1])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X2))
    | v5_pre_topc(X3,X2,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ( v1_funct_1(k9_tmap_1(X16,X17))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( v1_funct_2(k9_tmap_1(X16,X17),u1_struct_0(X16),u1_struct_0(k8_tmap_1(X16,X17)))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) )
      & ( m1_subset_1(k9_tmap_1(X16,X17),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(k8_tmap_1(X16,X17)))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k9_tmap_1])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ( ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))
      | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_19,plain,(
    ! [X14,X15] :
      ( ( v1_pre_topc(k8_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_pre_topc(X15,X14) )
      & ( v2_pre_topc(k8_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_pre_topc(X15,X14) )
      & ( l1_pre_topc(k8_tmap_1(X14,X15))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14)
        | ~ m1_pre_topc(X15,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k8_tmap_1])])])])).

cnf(c_0_20,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | m1_subset_1(esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)),u1_struct_0(X4))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_21,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( m1_subset_1(k9_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_funct_2(k9_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k8_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,plain,
    ( v1_funct_1(k9_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( v2_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( l1_pre_topc(k8_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | m1_subset_1(esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)),u1_struct_0(X4))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_16]),c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(k9_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(k9_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(k9_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_38,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_16]),c_0_25])])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_16])).

fof(c_0_42,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(X7,X6)
      | v2_pre_topc(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_43,plain,(
    ! [X19,X20] :
      ( ~ l1_pre_topc(X19)
      | ~ m1_pre_topc(X20,X19)
      | l1_pre_topc(X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_16]),c_0_25])])).

cnf(c_0_45,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_47,plain,(
    ! [X24,X25,X26] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X24)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | r1_tmap_1(X25,k8_tmap_1(X24,X25),k2_tmap_1(X24,k8_tmap_1(X24,X25),k9_tmap_1(X24,X25),X25),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t119_tmap_1])])])])).

cnf(c_0_48,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1),X1,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),X1,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),X1)),u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_16]),c_0_36])])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_23]),c_0_24]),c_0_25])])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_25])])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r1_tmap_1(X2,k8_tmap_1(X1,X2),k2_tmap_1(X1,k8_tmap_1(X1,X2),k9_tmap_1(X1,X2),X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])]),c_0_51])).

cnf(c_0_54,plain,
    ( v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,esk1_3(X2,X1,X3))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk3_0,k8_tmap_1(X1,esk3_0),k2_tmap_1(X1,k8_tmap_1(X1,esk3_0),k9_tmap_1(X1,esk3_0),esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_51])).

cnf(c_0_56,plain,
    ( v5_pre_topc(k2_tmap_1(X1,X2,X3,X4),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),esk1_3(X2,X4,k2_tmap_1(X1,X2,X3,X4)))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_15]),c_0_16]),c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | r1_tmap_1(esk3_0,k8_tmap_1(esk2_0,esk3_0),k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk1_3(k8_tmap_1(esk2_0,esk3_0),esk3_0,k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_23]),c_0_24]),c_0_25])]),c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_33]),c_0_34]),c_0_32]),c_0_35]),c_0_49]),c_0_36]),c_0_50])]),c_0_51])).

cnf(c_0_59,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_16]),c_0_25])])).

cnf(c_0_60,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_16]),c_0_25])])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_16]),c_0_50])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_16]),c_0_36])])).

cnf(c_0_65,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_21]),c_0_33]),c_0_34]),c_0_32])])).

cnf(c_0_67,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_16]),c_0_25])])).

cnf(c_0_68,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_16]),c_0_50])])).

cnf(c_0_69,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_16]),c_0_50])])).

cnf(c_0_70,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_16]),c_0_25])])).

cnf(c_0_71,negated_conjecture,
    ( ~ v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_16]),c_0_36])])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),esk3_0,k8_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_16]),c_0_36])])).

cnf(c_0_73,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0)))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_74,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_21]),c_0_33]),c_0_34]),c_0_32])])).

cnf(c_0_75,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_16]),c_0_50])])).

cnf(c_0_76,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_16]),c_0_25])])).

cnf(c_0_77,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk2_0,k8_tmap_1(esk2_0,esk3_0),k9_tmap_1(esk2_0,esk3_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(k8_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_16]),c_0_36])])).

cnf(c_0_78,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_15]),c_0_33]),c_0_34]),c_0_32])])).

cnf(c_0_79,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_16]),c_0_50])])).

fof(c_0_80,plain,(
    ! [X22,X23] :
      ( ( ~ v2_struct_0(k8_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X23,X22) )
      & ( v1_pre_topc(k8_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X23,X22) )
      & ( v2_pre_topc(k8_tmap_1(X22,X23))
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_pre_topc(X23,X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_tmap_1])])])])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0))
    | ~ l1_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_16]),c_0_25])])).

cnf(c_0_82,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k8_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( v2_struct_0(k8_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_16]),c_0_36])])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),
    [proof]).

%------------------------------------------------------------------------------
