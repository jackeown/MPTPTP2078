%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 255 expanded)
%              Number of clauses        :   36 (  79 expanded)
%              Number of leaves         :    7 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  294 (3299 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_tmap_1,conjecture,(
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
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X3,X1,X4,X6)
                              & v5_pre_topc(X5,X1,X2) )
                           => r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tmap_1)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(t52_tmap_1,axiom,(
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
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X7 = k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)
                                  & r1_tmap_1(X2,X3,X4,X6)
                                  & r1_tmap_1(X3,X1,X5,X7) )
                               => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).

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

fof(c_0_7,negated_conjecture,(
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
                  & v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ( ( r1_tmap_1(X3,X1,X4,X6)
                                & v5_pre_topc(X5,X1,X2) )
                             => r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_tmap_1])).

fof(c_0_8,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | r2_hidden(X18,k1_connsp_2(X17,X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
    & v5_pre_topc(esk6_0,esk2_0,esk3_0)
    & ~ r1_tmap_1(esk4_0,esk3_0,k1_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0,esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X8,X9,X10] :
      ( ~ r2_hidden(X8,X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | ~ v1_xboole_0(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_11,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | m1_subset_1(k1_connsp_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

cnf(c_0_17,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk7_0,k1_connsp_2(esk4_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X11,X12,X13,X14] :
      ( v1_xboole_0(X11)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,X11,X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ m1_subset_1(X14,X11)
      | m1_subset_1(k3_funct_2(X11,X12,X13,X14),X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

cnf(c_0_21,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(k1_connsp_2(esk4_0,esk7_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk4_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

fof(c_0_23,plain,(
    ! [X24,X25,X26,X27,X28,X29,X30] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X24))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X24))))
      | ~ m1_subset_1(X29,u1_struct_0(X25))
      | ~ m1_subset_1(X30,u1_struct_0(X26))
      | X30 != k3_funct_2(u1_struct_0(X25),u1_struct_0(X26),X27,X29)
      | ~ r1_tmap_1(X25,X26,X27,X29)
      | ~ r1_tmap_1(X26,X24,X28,X30)
      | r1_tmap_1(X25,X24,k1_partfun1(u1_struct_0(X25),u1_struct_0(X26),u1_struct_0(X26),u1_struct_0(X24),X27,X28),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_28,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_29,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ v5_pre_topc(X21,X20,X19)
        | ~ m1_subset_1(X22,u1_struct_0(X20))
        | r1_tmap_1(X20,X19,X21,X22)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X20),u1_struct_0(X19))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk1_3(X19,X20,X21),u1_struct_0(X20))
        | v5_pre_topc(X21,X20,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X20),u1_struct_0(X19))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ r1_tmap_1(X20,X19,X21,esk1_3(X19,X20,X21))
        | v5_pre_topc(X21,X20,X19)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X20),u1_struct_0(X19))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ m1_subset_1(X7,u1_struct_0(X3))
    | X7 != k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)
    | ~ r1_tmap_1(X2,X3,X4,X6)
    | ~ r1_tmap_1(X3,X1,X5,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_32,plain,
    ( r1_tmap_1(X2,X3,X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_43,plain,
    ( r1_tmap_1(X1,X2,k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X5,k3_funct_2(u1_struct_0(X1),u1_struct_0(X3),X4,X6))
    | ~ r1_tmap_1(X1,X3,X4,X6)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X3),X4,X6),u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_subset_1(X6,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40])]),c_0_41]),c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,k1_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(X1),esk5_0,X2),esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk2_0,X1,X2,k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35]),c_0_13]),c_0_37]),c_0_14]),c_0_25]),c_0_26]),c_0_45]),c_0_27]),c_0_12])]),c_0_15]),c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk6_0,k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk3_0,k1_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_34]),c_0_36]),c_0_38]),c_0_39]),c_0_40])]),c_0_49]),c_0_41]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:37:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.029 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t54_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((r1_tmap_1(X3,X1,X4,X6)&v5_pre_topc(X5,X1,X2))=>r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tmap_1)).
% 0.20/0.37  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.20/0.37  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.37  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.20/0.37  fof(dt_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 0.20/0.37  fof(t52_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X7=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)&r1_tmap_1(X2,X3,X4,X6))&r1_tmap_1(X3,X1,X5,X7))=>r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tmap_1)).
% 0.20/0.37  fof(t49_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 0.20/0.37  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((r1_tmap_1(X3,X1,X4,X6)&v5_pre_topc(X5,X1,X2))=>r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6))))))))), inference(assume_negation,[status(cth)],[t54_tmap_1])).
% 0.20/0.37  fof(c_0_8, plain, ![X17, X18]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~m1_subset_1(X18,u1_struct_0(X17))|r2_hidden(X18,k1_connsp_2(X17,X18)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.20/0.37  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&((r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)&v5_pre_topc(esk6_0,esk2_0,esk3_0))&~r1_tmap_1(esk4_0,esk3_0,k1_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0,esk6_0),esk7_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.20/0.37  fof(c_0_10, plain, ![X8, X9, X10]:(~r2_hidden(X8,X9)|~m1_subset_1(X9,k1_zfmisc_1(X10))|~v1_xboole_0(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.37  cnf(c_0_11, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.37  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_14, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  fof(c_0_16, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|~m1_subset_1(X16,u1_struct_0(X15))|m1_subset_1(k1_connsp_2(X15,X16),k1_zfmisc_1(u1_struct_0(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.20/0.37  cnf(c_0_17, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk7_0,k1_connsp_2(esk4_0,esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.37  cnf(c_0_19, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.37  fof(c_0_20, plain, ![X11, X12, X13, X14]:(v1_xboole_0(X11)|~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~m1_subset_1(X14,X11)|m1_subset_1(k3_funct_2(X11,X12,X13,X14),X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).
% 0.20/0.37  cnf(c_0_21, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(k1_connsp_2(esk4_0,esk7_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(k1_connsp_2(esk4_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.37  fof(c_0_23, plain, ![X24, X25, X26, X27, X28, X29, X30]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X24))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X24))))|(~m1_subset_1(X29,u1_struct_0(X25))|(~m1_subset_1(X30,u1_struct_0(X26))|(X30!=k3_funct_2(u1_struct_0(X25),u1_struct_0(X26),X27,X29)|~r1_tmap_1(X25,X26,X27,X29)|~r1_tmap_1(X26,X24,X28,X30)|r1_tmap_1(X25,X24,k1_partfun1(u1_struct_0(X25),u1_struct_0(X26),u1_struct_0(X26),u1_struct_0(X24),X27,X28),X29))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).
% 0.20/0.37  cnf(c_0_24, plain, (v1_xboole_0(X1)|m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_28, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.37  fof(c_0_29, plain, ![X19, X20, X21, X22]:((~v5_pre_topc(X21,X20,X19)|(~m1_subset_1(X22,u1_struct_0(X20))|r1_tmap_1(X20,X19,X21,X22))|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X20),u1_struct_0(X19))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&((m1_subset_1(esk1_3(X19,X20,X21),u1_struct_0(X20))|v5_pre_topc(X21,X20,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X20),u1_struct_0(X19))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)))&(~r1_tmap_1(X20,X19,X21,esk1_3(X19,X20,X21))|v5_pre_topc(X21,X20,X19)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X20),u1_struct_0(X19))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X19)))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).
% 0.20/0.37  cnf(c_0_30, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~m1_subset_1(X6,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X3))|X7!=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)|~r1_tmap_1(X2,X3,X4,X6)|~r1_tmap_1(X3,X1,X5,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (m1_subset_1(k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,X1),u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])]), c_0_28])).
% 0.20/0.37  cnf(c_0_32, plain, (r1_tmap_1(X2,X3,X1,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.37  cnf(c_0_33, negated_conjecture, (v5_pre_topc(esk6_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_37, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_43, plain, (r1_tmap_1(X1,X2,k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X5,k3_funct_2(u1_struct_0(X1),u1_struct_0(X3),X4,X6))|~r1_tmap_1(X1,X3,X4,X6)|~l1_pre_topc(X3)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))|~v1_funct_1(X5)|~v1_funct_1(X4)|~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X3),X4,X6),u1_struct_0(X3))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))|~m1_subset_1(X6,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_30])).
% 0.20/0.37  cnf(c_0_44, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_31, c_0_12])).
% 0.20/0.37  cnf(c_0_46, negated_conjecture, (r1_tmap_1(esk2_0,esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40])]), c_0_41]), c_0_42])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (r1_tmap_1(esk4_0,X1,k1_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(X1),esk5_0,X2),esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk2_0,X1,X2,k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0))|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_35]), c_0_13]), c_0_37]), c_0_14]), c_0_25]), c_0_26]), c_0_45]), c_0_27]), c_0_12])]), c_0_15]), c_0_42])).
% 0.20/0.37  cnf(c_0_48, negated_conjecture, (r1_tmap_1(esk2_0,esk3_0,esk6_0,k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0))), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, (~r1_tmap_1(esk4_0,esk3_0,k1_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk5_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.37  cnf(c_0_50, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_34]), c_0_36]), c_0_38]), c_0_39]), c_0_40])]), c_0_49]), c_0_41]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 51
% 0.20/0.37  # Proof object clause steps            : 36
% 0.20/0.37  # Proof object formula steps           : 15
% 0.20/0.37  # Proof object conjectures             : 32
% 0.20/0.37  # Proof object clause conjectures      : 29
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 25
% 0.20/0.37  # Proof object initial formulas used   : 7
% 0.20/0.37  # Proof object generating inferences   : 10
% 0.20/0.37  # Proof object simplifying inferences  : 43
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 7
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 27
% 0.20/0.37  # Removed in clause preprocessing      : 0
% 0.20/0.37  # Initial clauses in saturation        : 27
% 0.20/0.37  # Processed clauses                    : 85
% 0.20/0.37  # ...of these trivial                  : 0
% 0.20/0.37  # ...subsumed                          : 1
% 0.20/0.37  # ...remaining for further processing  : 84
% 0.20/0.37  # Other redundant clauses eliminated   : 1
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 0
% 0.20/0.37  # Generated clauses                    : 39
% 0.20/0.37  # ...of the previous two non-trivial   : 37
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 37
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 1
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 55
% 0.20/0.37  #    Positive orientable unit clauses  : 24
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 7
% 0.20/0.37  #    Non-unit-clauses                  : 24
% 0.20/0.37  # Current number of unprocessed clauses: 5
% 0.20/0.37  # ...number of literals in the above   : 25
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 28
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 436
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 22
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 18
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 3
% 0.20/0.37  # BW rewrite match successes           : 0
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 4820
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.033 s
% 0.20/0.37  # System time              : 0.007 s
% 0.20/0.37  # Total time               : 0.040 s
% 0.20/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
