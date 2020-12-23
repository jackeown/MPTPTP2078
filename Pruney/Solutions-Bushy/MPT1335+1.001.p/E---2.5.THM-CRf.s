%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1335+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:09 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 631 expanded)
%              Number of clauses        :   56 ( 216 expanded)
%              Number of leaves         :   11 ( 150 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 (5429 expanded)
%              Number of equality atoms :   16 (  71 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t58_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( ( v5_pre_topc(X4,X1,X3)
                          & v5_pre_topc(X5,X3,X2) )
                       => v5_pre_topc(k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(fc8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v1_xboole_0(X2)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X2,X3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k5_relat_1(X4,X5))
        & v1_funct_2(k5_relat_1(X4,X5),X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(t181_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => k10_relat_1(k5_relat_1(X2,X3),X1) = k10_relat_1(X2,k10_relat_1(X3,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(dt_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k8_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & l1_pre_topc(X3) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                       => ( ( v5_pre_topc(X4,X1,X3)
                            & v5_pre_topc(X5,X3,X2) )
                         => v5_pre_topc(k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X1,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t58_tops_2])).

fof(c_0_12,plain,(
    ! [X17,X18,X19,X20,X21,X22] :
      ( ( v1_funct_1(k1_partfun1(X17,X18,X19,X20,X21,X22))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( m1_subset_1(k1_partfun1(X17,X18,X19,X20,X21,X22),k1_zfmisc_1(k2_zfmisc_1(X17,X20)))
        | ~ v1_funct_1(X21)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
        | ~ v1_funct_1(X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

fof(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & l1_pre_topc(esk6_0)
    & ~ v2_struct_0(esk7_0)
    & l1_pre_topc(esk7_0)
    & v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk7_0))
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk7_0))))
    & v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0))))
    & v5_pre_topc(esk8_0,esk5_0,esk7_0)
    & v5_pre_topc(esk9_0,esk7_0,esk6_0)
    & ~ v5_pre_topc(k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk9_0),esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X38,X39,X40,X41,X42,X43] :
      ( ~ v1_funct_1(X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | ~ v1_funct_1(X43)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k1_partfun1(X38,X39,X40,X41,X42,X43) = k5_relat_1(X42,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

fof(c_0_15,plain,(
    ! [X33,X34,X35,X36,X37] :
      ( ( v1_funct_1(k5_relat_1(X36,X37))
        | v1_xboole_0(X34)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) )
      & ( v1_funct_2(k5_relat_1(X36,X37),X33,X35)
        | v1_xboole_0(X34)
        | ~ v1_funct_1(X36)
        | ~ v1_funct_2(X36,X33,X34)
        | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,X34,X35)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).

cnf(c_0_16,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( v1_funct_2(k5_relat_1(X1,X2),X3,X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk9_0,u1_struct_0(esk7_0),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(k1_partfun1(X1,X2,u1_struct_0(esk7_0),u1_struct_0(esk6_0),X3,esk9_0))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( k1_partfun1(X1,X2,u1_struct_0(esk7_0),u1_struct_0(esk6_0),X3,esk9_0) = k5_relat_1(X3,esk9_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_17]),c_0_18])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_27,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ v5_pre_topc(X14,X12,X13)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ v4_pre_topc(X15,X13)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14,X15),X12)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X13)))
        | v5_pre_topc(X14,X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( v4_pre_topc(esk1_3(X12,X13,X14),X13)
        | v5_pre_topc(X14,X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X12),u1_struct_0(X13),X14,esk1_3(X12,X13,X14)),X12)
        | v5_pre_topc(X14,X12,X13)
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,u1_struct_0(X12),u1_struct_0(X13))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X12),u1_struct_0(X13))))
        | ~ l1_pre_topc(X13)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_funct_2(k5_relat_1(X1,esk9_0),X2,u1_struct_0(esk6_0))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk7_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18]),c_0_17])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk5_0),u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk9_0) = k5_relat_1(esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_24])])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,u1_struct_0(esk7_0),u1_struct_0(esk6_0),X3,esk9_0),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk6_0))))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_17]),c_0_18])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v5_pre_topc(k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk7_0),u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk9_0),esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_35,plain,(
    ! [X48,X49,X50] :
      ( ~ v1_relat_1(X49)
      | ~ v1_relat_1(X50)
      | k10_relat_1(k5_relat_1(X49,X50),X48) = k10_relat_1(X49,k10_relat_1(X50,X48)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t181_relat_1])])])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v1_funct_2(k5_relat_1(esk8_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_24]),c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(k5_relat_1(esk8_0,esk9_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(k5_relat_1(esk8_0,esk9_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_32]),c_0_24])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v5_pre_topc(k5_relat_1(esk8_0,esk9_0),esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_44,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_45,plain,(
    ! [X44,X45,X46,X47] :
      ( ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
      | k8_relset_1(X44,X45,X46,X47) = k10_relat_1(X46,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

fof(c_0_46,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
      | m1_subset_1(k8_relset_1(X23,X24,X25,X26),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k8_relset_1])])).

cnf(c_0_47,plain,
    ( k10_relat_1(k5_relat_1(X1,X2),X3) = k10_relat_1(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_49,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v4_pre_topc(esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | m1_subset_1(esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_52,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( m1_subset_1(k8_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk8_0,X1),X2) = k10_relat_1(esk8_0,k10_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_17])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk6_0),X2,esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0))),X1)
    | ~ v5_pre_topc(X2,X1,esk6_0)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk6_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk6_0)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_40])]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( v5_pre_topc(esk9_0,esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk9_0,X1) = k10_relat_1(esk9_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k8_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(k5_relat_1(esk8_0,esk9_0),X1) = k10_relat_1(esk8_0,k10_relat_1(esk9_0,X1)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v4_pre_topc(k10_relat_1(esk9_0,esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0))),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_58]),c_0_21]),c_0_18]),c_0_59]),c_0_17])])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(k10_relat_1(esk9_0,X1),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_58])).

cnf(c_0_64,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk6_0),k5_relat_1(esk8_0,esk9_0),X1) = k10_relat_1(esk8_0,k10_relat_1(esk9_0,X1)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_42]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk7_0),X2,k10_relat_1(esk9_0,esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0)))),X1)
    | ~ v5_pre_topc(X2,X1,esk7_0)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk7_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk7_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_62]),c_0_59]),c_0_63])])).

cnf(c_0_67,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_68,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk5_0),u1_struct_0(esk7_0),esk8_0,X1) = k10_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_23])).

fof(c_0_69,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v4_pre_topc(k10_relat_1(esk8_0,k10_relat_1(esk9_0,esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0)))),esk5_0)
    | ~ v1_funct_2(k5_relat_1(esk8_0,esk9_0),u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0))
    | v4_pre_topc(k10_relat_1(esk8_0,k10_relat_1(esk9_0,esk1_3(esk5_0,esk6_0,k5_relat_1(esk8_0,esk9_0)))),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_30]),c_0_24]),c_0_41]),c_0_23])])).

cnf(c_0_72,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_38])).

cnf(c_0_74,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_75,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_76,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74])).

cnf(c_0_77,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_59])]),
    [proof]).

%------------------------------------------------------------------------------
