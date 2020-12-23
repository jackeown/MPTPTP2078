%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:15 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.75s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 962 expanded)
%              Number of clauses        :   69 ( 335 expanded)
%              Number of leaves         :   14 ( 240 expanded)
%              Depth                    :   19
%              Number of atoms          :  479 (10043 expanded)
%              Number of equality atoms :   34 ( 498 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   25 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_2)).

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

fof(d4_tmap_1,axiom,(
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
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t72_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(X1,X2)
       => k1_funct_1(k7_relat_1(X3,X2),X1) = k1_funct_1(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_funct_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                       => ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( r2_hidden(X6,u1_struct_0(X3))
                               => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_tmap_1])).

fof(c_0_15,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_pre_topc(X35,X34)
      | l1_pre_topc(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,negated_conjecture,(
    ! [X53] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X53,u1_struct_0(esk3_0))
        | ~ r2_hidden(X53,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X53) = k1_funct_1(esk6_0,X53) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( ~ r2_funct_2(X15,X16,X17,X18)
        | ~ m1_subset_1(X19,X15)
        | k1_funct_1(X17,X19) = k1_funct_1(X18,X19)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( m1_subset_1(esk1_4(X15,X16,X17,X18),X15)
        | r2_funct_2(X15,X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( k1_funct_1(X17,esk1_4(X15,X16,X17,X18)) != k1_funct_1(X18,esk1_4(X15,X16,X17,X18))
        | r2_funct_2(X15,X16,X17,X18)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

fof(c_0_18,plain,(
    ! [X44,X45,X46,X47] :
      ( ( v1_funct_1(k2_tmap_1(X44,X45,X46,X47))
        | ~ l1_struct_0(X44)
        | ~ l1_struct_0(X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | ~ l1_struct_0(X47) )
      & ( v1_funct_2(k2_tmap_1(X44,X45,X46,X47),u1_struct_0(X47),u1_struct_0(X45))
        | ~ l1_struct_0(X44)
        | ~ l1_struct_0(X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | ~ l1_struct_0(X47) )
      & ( m1_subset_1(k2_tmap_1(X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ l1_struct_0(X44)
        | ~ l1_struct_0(X45)
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))
        | ~ l1_struct_0(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_19,plain,(
    ! [X33] :
      ( ~ l1_pre_topc(X33)
      | l1_struct_0(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X40,X41,X42,X43] :
      ( v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
      | ~ m1_pre_topc(X43,X40)
      | k2_tmap_1(X40,X41,X42,X43) = k2_partfun1(u1_struct_0(X40),u1_struct_0(X41),X42,u1_struct_0(X43)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),X1)
    | r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X25,X26,X27,X28] :
      ( ~ v1_funct_1(X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_partfun1(X25,X26,X27,X28) = k7_relat_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_40,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | v1_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_41,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))
    | m1_subset_1(esk1_4(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1)),u1_struct_0(X1))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_44,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_47,plain,(
    ! [X9,X10,X11] :
      ( ~ v1_relat_1(X11)
      | ~ v1_funct_1(X11)
      | ~ r2_hidden(X9,X10)
      | k1_funct_1(k7_relat_1(X11,X10),X9) = k1_funct_1(X11,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).

cnf(c_0_48,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_30]),c_0_22]),c_0_36]),c_0_37])]),c_0_38]),c_0_39])).

cnf(c_0_50,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_51,plain,(
    ! [X21,X22,X23,X24] :
      ( ( v1_funct_1(k2_partfun1(X21,X22,X23,X24))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( m1_subset_1(k2_partfun1(X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_52,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ m1_pre_topc(X38,X37)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | m1_subset_1(X39,u1_struct_0(X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0)),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_54,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_22])).

cnf(c_0_55,plain,
    ( k1_funct_1(k7_relat_1(X1,X3),X2) = k1_funct_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( k7_relat_1(esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_37]),c_0_33])])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_33])).

cnf(c_0_58,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_59,plain,(
    ! [X7,X8] :
      ( ~ m1_subset_1(X7,X8)
      | v1_xboole_0(X8)
      | r2_hidden(X7,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_60,plain,(
    ! [X29,X30,X31,X32] :
      ( v1_xboole_0(X29)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X29,X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | ~ m1_subset_1(X32,X29)
      | k3_funct_2(X29,X30,X31,X32) = k1_funct_1(X31,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_33]),c_0_54]),c_0_36]),c_0_37])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_64,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1),X2) = k1_funct_1(esk5_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_37]),c_0_57])])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_49]),c_0_37]),c_0_33])])).

cnf(c_0_67,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_68,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(X1))
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r2_funct_2(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4))
    | k1_funct_1(X3,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4))) != k1_funct_1(esk5_0,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)))
    | ~ m1_pre_topc(X4,esk3_0)
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)),u1_struct_0(X4))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk5_0,X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_33]),c_0_36]),c_0_37])])).

cnf(c_0_73,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_21]),c_0_22])]),c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_21]),c_0_45]),c_0_46]),c_0_42])])).

cnf(c_0_75,plain,
    ( k1_funct_1(X3,X5) = k1_funct_1(X4,X5)
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ m1_subset_1(X5,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_76,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_77,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) = k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_27]),c_0_43]),c_0_44]),c_0_54]),c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_79,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_42]),c_0_45]),c_0_46])])).

cnf(c_0_80,plain,
    ( k1_funct_1(X1,X2) = k1_funct_1(k2_tmap_1(X3,X4,X5,X6),X2)
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X4)
    | ~ l1_struct_0(X3)
    | ~ r2_funct_2(u1_struct_0(X6),u1_struct_0(X4),X1,k2_tmap_1(X3,X4,X5,X6))
    | ~ v1_funct_2(X1,u1_struct_0(X6),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X4))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,u1_struct_0(X6)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) = k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))
    | r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) != k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_25]),c_0_43]),c_0_44]),c_0_54]),c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_83,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(k2_tmap_1(X1,esk2_0,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_25]),c_0_43]),c_0_44])])).

cnf(c_0_84,plain,
    ( r2_funct_2(X1,X2,X3,X4)
    | k1_funct_1(X3,esk1_4(X1,X2,X3,X4)) != k1_funct_1(k2_tmap_1(X5,X6,X7,X8),esk1_4(X1,X2,X3,X4))
    | ~ l1_struct_0(X8)
    | ~ l1_struct_0(X6)
    | ~ l1_struct_0(X5)
    | ~ r2_funct_2(u1_struct_0(X8),u1_struct_0(X6),X4,k2_tmap_1(X5,X6,X7,X8))
    | ~ v1_funct_2(X4,u1_struct_0(X8),u1_struct_0(X6))
    | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
    | ~ v1_funct_2(X4,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X7)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
    | ~ m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X8))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_71]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)
    | m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_27]),c_0_43]),c_0_44])])).

cnf(c_0_87,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_88,negated_conjecture,
    ( r2_funct_2(X1,X2,X3,esk6_0)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | k1_funct_1(X3,esk1_4(X1,X2,X3,esk6_0)) != k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk1_4(X1,X2,X3,esk6_0))
    | ~ v1_funct_2(esk6_0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(esk1_4(X1,X2,X3,esk6_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_43]),c_0_44]),c_0_54]),c_0_45]),c_0_36]),c_0_46]),c_0_37]),c_0_42]),c_0_33])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_33]),c_0_54]),c_0_36]),c_0_37])]),c_0_87])).

cnf(c_0_90,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_45]),c_0_42])]),c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_26]),c_0_43]),c_0_44]),c_0_54]),c_0_36]),c_0_37]),c_0_33])])).

fof(c_0_92,plain,(
    ! [X36] :
      ( v2_struct_0(X36)
      | ~ l1_struct_0(X36)
      | ~ v1_xboole_0(u1_struct_0(X36)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_93,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_27]),c_0_43]),c_0_44]),c_0_54]),c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_94,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_25]),c_0_43]),c_0_44]),c_0_54]),c_0_36]),c_0_37]),c_0_33])])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_43])]),c_0_63])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_96]),c_0_54])]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 5.75/5.97  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 5.75/5.97  # and selection function PSelectComplexExceptRRHorn.
% 5.75/5.97  #
% 5.75/5.97  # Preprocessing time       : 0.039 s
% 5.75/5.97  # Presaturation interreduction done
% 5.75/5.97  
% 5.75/5.97  # Proof found!
% 5.75/5.97  # SZS status Theorem
% 5.75/5.97  # SZS output start CNFRefutation
% 5.75/5.97  fof(t59_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 5.75/5.97  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.75/5.97  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_2)).
% 5.75/5.97  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 5.75/5.97  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.75/5.97  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.75/5.97  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.75/5.97  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.75/5.97  fof(t72_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(X1,X2)=>k1_funct_1(k7_relat_1(X3,X2),X1)=k1_funct_1(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_funct_1)).
% 5.75/5.97  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.75/5.97  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 5.75/5.97  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.75/5.97  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.75/5.97  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.75/5.97  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t59_tmap_1])).
% 5.75/5.97  fof(c_0_15, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_pre_topc(X35,X34)|l1_pre_topc(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 5.75/5.97  fof(c_0_16, negated_conjecture, ![X53]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X53,u1_struct_0(esk3_0))|(~r2_hidden(X53,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X53)=k1_funct_1(esk6_0,X53)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 5.75/5.97  fof(c_0_17, plain, ![X15, X16, X17, X18, X19]:((~r2_funct_2(X15,X16,X17,X18)|(~m1_subset_1(X19,X15)|k1_funct_1(X17,X19)=k1_funct_1(X18,X19))|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))|(~v1_funct_1(X17)|~v1_funct_2(X17,X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&((m1_subset_1(esk1_4(X15,X16,X17,X18),X15)|r2_funct_2(X15,X16,X17,X18)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))|(~v1_funct_1(X17)|~v1_funct_2(X17,X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(k1_funct_1(X17,esk1_4(X15,X16,X17,X18))!=k1_funct_1(X18,esk1_4(X15,X16,X17,X18))|r2_funct_2(X15,X16,X17,X18)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))|(~v1_funct_1(X17)|~v1_funct_2(X17,X15,X16)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 5.75/5.97  fof(c_0_18, plain, ![X44, X45, X46, X47]:(((v1_funct_1(k2_tmap_1(X44,X45,X46,X47))|(~l1_struct_0(X44)|~l1_struct_0(X45)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|~l1_struct_0(X47)))&(v1_funct_2(k2_tmap_1(X44,X45,X46,X47),u1_struct_0(X47),u1_struct_0(X45))|(~l1_struct_0(X44)|~l1_struct_0(X45)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|~l1_struct_0(X47))))&(m1_subset_1(k2_tmap_1(X44,X45,X46,X47),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))|(~l1_struct_0(X44)|~l1_struct_0(X45)|~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X44),u1_struct_0(X45))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X45))))|~l1_struct_0(X47)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 5.75/5.97  fof(c_0_19, plain, ![X33]:(~l1_pre_topc(X33)|l1_struct_0(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 5.75/5.97  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 5.75/5.97  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  fof(c_0_23, plain, ![X40, X41, X42, X43]:(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))|(~m1_pre_topc(X43,X40)|k2_tmap_1(X40,X41,X42,X43)=k2_partfun1(u1_struct_0(X40),u1_struct_0(X41),X42,u1_struct_0(X43)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 5.75/5.97  cnf(c_0_24, plain, (m1_subset_1(esk1_4(X1,X2,X3,X4),X1)|r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.75/5.97  cnf(c_0_25, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.75/5.97  cnf(c_0_26, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.75/5.97  cnf(c_0_27, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 5.75/5.97  cnf(c_0_28, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 5.75/5.97  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 5.75/5.97  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  fof(c_0_31, plain, ![X25, X26, X27, X28]:(~v1_funct_1(X27)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|k2_partfun1(X25,X26,X27,X28)=k7_relat_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 5.75/5.97  cnf(c_0_32, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 5.75/5.97  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  fof(c_0_40, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|v1_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 5.75/5.97  cnf(c_0_41, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1))|m1_subset_1(esk1_4(u1_struct_0(X1),u1_struct_0(X2),X3,k2_tmap_1(X4,X2,X5,X1)),u1_struct_0(X1))|~l1_struct_0(X1)|~l1_struct_0(X2)|~l1_struct_0(X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X3)|~v1_funct_1(X5)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])).
% 5.75/5.97  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_43, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 5.75/5.97  cnf(c_0_44, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_30])).
% 5.75/5.97  cnf(c_0_45, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  fof(c_0_47, plain, ![X9, X10, X11]:(~v1_relat_1(X11)|~v1_funct_1(X11)|(~r2_hidden(X9,X10)|k1_funct_1(k7_relat_1(X11,X10),X9)=k1_funct_1(X11,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t72_funct_1])])).
% 5.75/5.97  cnf(c_0_48, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 5.75/5.97  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_30]), c_0_22]), c_0_36]), c_0_37])]), c_0_38]), c_0_39])).
% 5.75/5.97  cnf(c_0_50, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 5.75/5.97  fof(c_0_51, plain, ![X21, X22, X23, X24]:((v1_funct_1(k2_partfun1(X21,X22,X23,X24))|(~v1_funct_1(X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&(m1_subset_1(k2_partfun1(X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|(~v1_funct_1(X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 5.75/5.97  fof(c_0_52, plain, ![X37, X38, X39]:(v2_struct_0(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~m1_pre_topc(X38,X37)|(~m1_subset_1(X39,u1_struct_0(X38))|m1_subset_1(X39,u1_struct_0(X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 5.75/5.97  cnf(c_0_53, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(X1,esk2_0,X2,esk4_0)),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])])).
% 5.75/5.97  cnf(c_0_54, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_22])).
% 5.75/5.97  cnf(c_0_55, plain, (k1_funct_1(k7_relat_1(X1,X3),X2)=k1_funct_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 5.75/5.97  cnf(c_0_56, negated_conjecture, (k7_relat_1(esk5_0,u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_37]), c_0_33])])).
% 5.75/5.97  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_50, c_0_33])).
% 5.75/5.97  cnf(c_0_58, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 5.75/5.97  fof(c_0_59, plain, ![X7, X8]:(~m1_subset_1(X7,X8)|(v1_xboole_0(X8)|r2_hidden(X7,X8))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 5.75/5.97  fof(c_0_60, plain, ![X29, X30, X31, X32]:(v1_xboole_0(X29)|~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|~m1_subset_1(X32,X29)|k3_funct_2(X29,X30,X31,X32)=k1_funct_1(X31,X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 5.75/5.97  cnf(c_0_61, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 5.75/5.97  cnf(c_0_62, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_33]), c_0_54]), c_0_36]), c_0_37])])).
% 5.75/5.97  cnf(c_0_63, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_64, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.75/5.97  cnf(c_0_65, negated_conjecture, (k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1),X2)=k1_funct_1(esk5_0,X2)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(X2,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_37]), c_0_57])])).
% 5.75/5.97  cnf(c_0_66, negated_conjecture, (v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X1))|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_49]), c_0_37]), c_0_33])])).
% 5.75/5.97  cnf(c_0_67, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 5.75/5.97  cnf(c_0_68, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 5.75/5.97  cnf(c_0_69, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(X1))|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])).
% 5.75/5.97  cnf(c_0_70, negated_conjecture, (r2_funct_2(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4))|k1_funct_1(X3,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)))!=k1_funct_1(esk5_0,esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)))|~m1_pre_topc(X4,esk3_0)|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~r2_hidden(esk1_4(X1,X2,X3,k2_tmap_1(esk3_0,esk2_0,esk5_0,X4)),u1_struct_0(X4))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_66])).
% 5.75/5.97  cnf(c_0_71, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_67, c_0_62])).
% 5.75/5.97  cnf(c_0_72, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1)=k1_funct_1(esk5_0,X1)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_33]), c_0_36]), c_0_37])])).
% 5.75/5.97  cnf(c_0_73, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_21]), c_0_22])]), c_0_39])).
% 5.75/5.97  cnf(c_0_74, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_21]), c_0_45]), c_0_46]), c_0_42])])).
% 5.75/5.97  cnf(c_0_75, plain, (k1_funct_1(X3,X5)=k1_funct_1(X4,X5)|~r2_funct_2(X1,X2,X3,X4)|~m1_subset_1(X5,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 5.75/5.97  cnf(c_0_76, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1)=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_77, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))=k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 5.75/5.97  cnf(c_0_78, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_27]), c_0_43]), c_0_44]), c_0_54]), c_0_36]), c_0_37]), c_0_33])])).
% 5.75/5.97  cnf(c_0_79, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),X1,esk6_0),u1_struct_0(esk4_0))|~v1_funct_2(X1,u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_42]), c_0_45]), c_0_46])])).
% 5.75/5.97  cnf(c_0_80, plain, (k1_funct_1(X1,X2)=k1_funct_1(k2_tmap_1(X3,X4,X5,X6),X2)|~l1_struct_0(X6)|~l1_struct_0(X4)|~l1_struct_0(X3)|~r2_funct_2(u1_struct_0(X6),u1_struct_0(X4),X1,k2_tmap_1(X3,X4,X5,X6))|~v1_funct_2(X1,u1_struct_0(X6),u1_struct_0(X4))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))|~v1_funct_1(X1)|~v1_funct_1(X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X4))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))|~m1_subset_1(X2,u1_struct_0(X6))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_25]), c_0_26]), c_0_27])).
% 5.75/5.97  cnf(c_0_81, negated_conjecture, (k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))|r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~r2_hidden(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_73])).
% 5.75/5.97  cnf(c_0_82, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(esk5_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))!=k1_funct_1(esk6_0,esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_25]), c_0_43]), c_0_44]), c_0_54]), c_0_36]), c_0_37]), c_0_33])])).
% 5.75/5.97  cnf(c_0_83, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(k2_tmap_1(X1,esk2_0,X2,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_25]), c_0_43]), c_0_44])])).
% 5.75/5.97  cnf(c_0_84, plain, (r2_funct_2(X1,X2,X3,X4)|k1_funct_1(X3,esk1_4(X1,X2,X3,X4))!=k1_funct_1(k2_tmap_1(X5,X6,X7,X8),esk1_4(X1,X2,X3,X4))|~l1_struct_0(X8)|~l1_struct_0(X6)|~l1_struct_0(X5)|~r2_funct_2(u1_struct_0(X8),u1_struct_0(X6),X4,k2_tmap_1(X5,X6,X7,X8))|~v1_funct_2(X4,u1_struct_0(X8),u1_struct_0(X6))|~v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))|~v1_funct_2(X4,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X4)|~v1_funct_1(X3)|~v1_funct_1(X7)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X6))))|~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))|~m1_subset_1(esk1_4(X1,X2,X3,X4),u1_struct_0(X8))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_64, c_0_80])).
% 5.75/5.97  cnf(c_0_85, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_71]), c_0_82])).
% 5.75/5.97  cnf(c_0_86, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0)|m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk4_0),esk6_0),u1_struct_0(esk4_0))|~l1_struct_0(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(X1,esk2_0,X2,esk4_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_27]), c_0_43]), c_0_44])])).
% 5.75/5.97  cnf(c_0_87, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 5.75/5.97  cnf(c_0_88, negated_conjecture, (r2_funct_2(X1,X2,X3,esk6_0)|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|k1_funct_1(X3,esk1_4(X1,X2,X3,esk6_0))!=k1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk1_4(X1,X2,X3,esk6_0))|~v1_funct_2(esk6_0,X1,X2)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(esk1_4(X1,X2,X3,esk6_0),u1_struct_0(esk4_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_43]), c_0_44]), c_0_54]), c_0_45]), c_0_36]), c_0_46]), c_0_37]), c_0_42]), c_0_33])])).
% 5.75/5.97  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk1_4(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0),u1_struct_0(esk4_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_33]), c_0_54]), c_0_36]), c_0_37])]), c_0_87])).
% 5.75/5.97  cnf(c_0_90, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_89]), c_0_45]), c_0_42])]), c_0_87])).
% 5.75/5.97  cnf(c_0_91, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|~v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_26]), c_0_43]), c_0_44]), c_0_54]), c_0_36]), c_0_37]), c_0_33])])).
% 5.75/5.97  fof(c_0_92, plain, ![X36]:(v2_struct_0(X36)|~l1_struct_0(X36)|~v1_xboole_0(u1_struct_0(X36))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 5.75/5.97  cnf(c_0_93, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_27]), c_0_43]), c_0_44]), c_0_54]), c_0_36]), c_0_37]), c_0_33])])).
% 5.75/5.97  cnf(c_0_94, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 5.75/5.97  cnf(c_0_95, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_25]), c_0_43]), c_0_44]), c_0_54]), c_0_36]), c_0_37]), c_0_33])])).
% 5.75/5.97  cnf(c_0_96, negated_conjecture, (v1_xboole_0(u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_43])]), c_0_63])).
% 5.75/5.97  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_96]), c_0_54])]), c_0_39]), ['proof']).
% 5.75/5.97  # SZS output end CNFRefutation
% 5.75/5.97  # Proof object total steps             : 98
% 5.75/5.97  # Proof object clause steps            : 69
% 5.75/5.97  # Proof object formula steps           : 29
% 5.75/5.97  # Proof object conjectures             : 52
% 5.75/5.97  # Proof object clause conjectures      : 49
% 5.75/5.97  # Proof object formula conjectures     : 3
% 5.75/5.97  # Proof object initial clauses used    : 33
% 5.75/5.97  # Proof object initial formulas used   : 14
% 5.75/5.97  # Proof object generating inferences   : 36
% 5.75/5.97  # Proof object simplifying inferences  : 117
% 5.75/5.97  # Training examples: 0 positive, 0 negative
% 5.75/5.97  # Parsed axioms                        : 14
% 5.75/5.97  # Removed by relevancy pruning/SinE    : 0
% 5.75/5.97  # Initial clauses                      : 34
% 5.75/5.97  # Removed in clause preprocessing      : 0
% 5.75/5.97  # Initial clauses in saturation        : 34
% 5.75/5.97  # Processed clauses                    : 12377
% 5.75/5.97  # ...of these trivial                  : 15
% 5.75/5.97  # ...subsumed                          : 7551
% 5.75/5.97  # ...remaining for further processing  : 4811
% 5.75/5.97  # Other redundant clauses eliminated   : 0
% 5.75/5.97  # Clauses deleted for lack of memory   : 0
% 5.75/5.97  # Backward-subsumed                    : 1149
% 5.75/5.97  # Backward-rewritten                   : 86
% 5.75/5.97  # Generated clauses                    : 105323
% 5.75/5.97  # ...of the previous two non-trivial   : 105116
% 5.75/5.97  # Contextual simplify-reflections      : 1933
% 5.75/5.97  # Paramodulations                      : 105170
% 5.75/5.97  # Factorizations                       : 2
% 5.75/5.97  # Equation resolutions                 : 151
% 5.75/5.97  # Propositional unsat checks           : 0
% 5.75/5.97  #    Propositional check models        : 0
% 5.75/5.97  #    Propositional check unsatisfiable : 0
% 5.75/5.97  #    Propositional clauses             : 0
% 5.75/5.97  #    Propositional clauses after purity: 0
% 5.75/5.97  #    Propositional unsat core size     : 0
% 5.75/5.97  #    Propositional preprocessing time  : 0.000
% 5.75/5.97  #    Propositional encoding time       : 0.000
% 5.75/5.97  #    Propositional solver time         : 0.000
% 5.75/5.97  #    Success case prop preproc time    : 0.000
% 5.75/5.97  #    Success case prop encoding time   : 0.000
% 5.75/5.97  #    Success case prop solver time     : 0.000
% 5.75/5.97  # Current number of processed clauses  : 3542
% 5.75/5.97  #    Positive orientable unit clauses  : 60
% 5.75/5.97  #    Positive unorientable unit clauses: 0
% 5.75/5.97  #    Negative unit clauses             : 4
% 5.75/5.97  #    Non-unit-clauses                  : 3478
% 5.75/5.97  # Current number of unprocessed clauses: 92329
% 5.75/5.97  # ...number of literals in the above   : 1529037
% 5.75/5.97  # Current number of archived formulas  : 0
% 5.75/5.97  # Current number of archived clauses   : 1269
% 5.75/5.97  # Clause-clause subsumption calls (NU) : 8525931
% 5.75/5.97  # Rec. Clause-clause subsumption calls : 328166
% 5.75/5.97  # Non-unit clause-clause subsumptions  : 10616
% 5.75/5.97  # Unit Clause-clause subsumption calls : 19920
% 5.75/5.97  # Rewrite failures with RHS unbound    : 0
% 5.75/5.97  # BW rewrite match attempts            : 2337
% 5.75/5.97  # BW rewrite match successes           : 13
% 5.75/5.97  # Condensation attempts                : 0
% 5.75/5.97  # Condensation successes               : 0
% 5.75/5.97  # Termbank termtop insertions          : 9953573
% 5.75/5.98  
% 5.75/5.98  # -------------------------------------------------
% 5.75/5.98  # User time                : 5.524 s
% 5.75/5.98  # System time              : 0.107 s
% 5.75/5.98  # Total time               : 5.631 s
% 5.75/5.98  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
