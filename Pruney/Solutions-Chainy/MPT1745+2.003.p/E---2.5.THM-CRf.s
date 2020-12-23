%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:13 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 175 expanded)
%              Number of clauses        :   34 (  52 expanded)
%              Number of leaves         :    6 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  278 (2366 expanded)
%              Number of equality atoms :    5 (   5 expanded)
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

fof(rc7_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2)
          & v4_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

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

fof(cc1_subset_1,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

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

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X14] :
      ( ( m1_subset_1(esk1_1(X14),k1_zfmisc_1(u1_struct_0(X14)))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( ~ v1_xboole_0(esk1_1(X14))
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) )
      & ( v4_pre_topc(esk1_1(X14),X14)
        | v2_struct_0(X14)
        | ~ v2_pre_topc(X14)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)
    & v5_pre_topc(esk7_0,esk3_0,esk4_0)
    & ~ r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ v5_pre_topc(X18,X17,X16)
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | r1_tmap_1(X17,X16,X18,X19)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( m1_subset_1(esk2_3(X16,X17,X18),u1_struct_0(X17))
        | v5_pre_topc(X18,X17,X16)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) )
      & ( ~ r1_tmap_1(X17,X16,X18,esk2_3(X16,X17,X18))
        | v5_pre_topc(X18,X17,X16)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))
        | v2_struct_0(X17)
        | ~ v2_pre_topc(X17)
        | ~ l1_pre_topc(X17)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

fof(c_0_10,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_xboole_0(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).

cnf(c_0_11,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_15,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))
      | ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X21))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
      | ~ m1_subset_1(X26,u1_struct_0(X22))
      | ~ m1_subset_1(X27,u1_struct_0(X23))
      | X27 != k3_funct_2(u1_struct_0(X22),u1_struct_0(X23),X24,X26)
      | ~ r1_tmap_1(X22,X23,X24,X26)
      | ~ r1_tmap_1(X23,X21,X25,X27)
      | r1_tmap_1(X22,X21,k1_partfun1(u1_struct_0(X22),u1_struct_0(X23),u1_struct_0(X23),u1_struct_0(X21),X24,X25),X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( v5_pre_topc(esk7_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk4_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_26])).

fof(c_0_31,plain,(
    ! [X10,X11,X12,X13] :
      ( v1_xboole_0(X10)
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,X10,X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ m1_subset_1(X13,X10)
      | m1_subset_1(k3_funct_2(X10,X11,X12,X13),X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk1_1(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(esk1_1(esk5_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k1_partfun1(u1_struct_0(X1),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),X2,esk7_0),X3)
    | v2_struct_0(X1)
    | X4 != k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3)
    | ~ r1_tmap_1(X1,esk3_0,X2,X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X4,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_17]),c_0_20]),c_0_19]),c_0_22]),c_0_21]),c_0_23]),c_0_24])]),c_0_26]),c_0_25]),c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),X1)
    | X2 != k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)
    | ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_12]),c_0_13]),c_0_36]),c_0_37])]),c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_36]),c_0_37])]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),X1)
    | ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.14/0.37  # and selection function PSelectComplexExceptRRHorn.
% 0.14/0.37  #
% 0.14/0.37  # Preprocessing time       : 0.029 s
% 0.14/0.37  # Presaturation interreduction done
% 0.14/0.37  
% 0.14/0.37  # Proof found!
% 0.14/0.37  # SZS status Theorem
% 0.14/0.37  # SZS output start CNFRefutation
% 0.14/0.37  fof(t54_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((r1_tmap_1(X3,X1,X4,X6)&v5_pre_topc(X5,X1,X2))=>r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tmap_1)).
% 0.14/0.37  fof(rc7_pre_topc, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>?[X2]:((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))&v4_pre_topc(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc7_pre_topc)).
% 0.14/0.37  fof(t49_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 0.14/0.37  fof(cc1_subset_1, axiom, ![X1]:(v1_xboole_0(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 0.14/0.37  fof(t52_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>(((X7=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)&r1_tmap_1(X2,X3,X4,X6))&r1_tmap_1(X3,X1,X5,X7))=>r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tmap_1)).
% 0.14/0.37  fof(dt_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 0.14/0.37  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((r1_tmap_1(X3,X1,X4,X6)&v5_pre_topc(X5,X1,X2))=>r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6))))))))), inference(assume_negation,[status(cth)],[t54_tmap_1])).
% 0.14/0.37  fof(c_0_7, plain, ![X14]:(((m1_subset_1(esk1_1(X14),k1_zfmisc_1(u1_struct_0(X14)))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))&(~v1_xboole_0(esk1_1(X14))|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14))))&(v4_pre_topc(esk1_1(X14),X14)|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc7_pre_topc])])])])])).
% 0.14/0.37  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)&v5_pre_topc(esk7_0,esk3_0,esk4_0))&~r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),esk8_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).
% 0.14/0.37  fof(c_0_9, plain, ![X16, X17, X18, X19]:((~v5_pre_topc(X18,X17,X16)|(~m1_subset_1(X19,u1_struct_0(X17))|r1_tmap_1(X17,X16,X18,X19))|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X17),u1_struct_0(X16))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16)))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&((m1_subset_1(esk2_3(X16,X17,X18),u1_struct_0(X17))|v5_pre_topc(X18,X17,X16)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X17),u1_struct_0(X16))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16)))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)))&(~r1_tmap_1(X17,X16,X18,esk2_3(X16,X17,X18))|v5_pre_topc(X18,X17,X16)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X17),u1_struct_0(X16))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16)))))|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).
% 0.14/0.37  fof(c_0_10, plain, ![X8, X9]:(~v1_xboole_0(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_subset_1])])])).
% 0.14/0.37  cnf(c_0_11, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_12, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  fof(c_0_15, plain, ![X21, X22, X23, X24, X25, X26, X27]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X23))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X23))))|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X21))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))|(~m1_subset_1(X26,u1_struct_0(X22))|(~m1_subset_1(X27,u1_struct_0(X23))|(X27!=k3_funct_2(u1_struct_0(X22),u1_struct_0(X23),X24,X26)|~r1_tmap_1(X22,X23,X24,X26)|~r1_tmap_1(X23,X21,X25,X27)|r1_tmap_1(X22,X21,k1_partfun1(u1_struct_0(X22),u1_struct_0(X23),u1_struct_0(X23),u1_struct_0(X21),X24,X25),X26))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).
% 0.14/0.37  cnf(c_0_16, plain, (r1_tmap_1(X2,X3,X1,X4)|v2_struct_0(X2)|v2_struct_0(X3)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_18, negated_conjecture, (v5_pre_topc(esk7_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_27, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14])).
% 0.14/0.37  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~m1_subset_1(X6,u1_struct_0(X2))|~m1_subset_1(X7,u1_struct_0(X3))|X7!=k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)|~r1_tmap_1(X2,X3,X4,X6)|~r1_tmap_1(X3,X1,X5,X7)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.37  cnf(c_0_30, negated_conjecture, (r1_tmap_1(esk3_0,esk4_0,esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25]), c_0_26])).
% 0.14/0.37  fof(c_0_31, plain, ![X10, X11, X12, X13]:(v1_xboole_0(X10)|~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~m1_subset_1(X13,X10)|m1_subset_1(k3_funct_2(X10,X11,X12,X13),X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).
% 0.14/0.37  cnf(c_0_32, plain, (v2_struct_0(X1)|~v1_xboole_0(esk1_1(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.37  cnf(c_0_33, negated_conjecture, (v1_xboole_0(esk1_1(esk5_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.37  cnf(c_0_34, negated_conjecture, (r1_tmap_1(X1,esk4_0,k1_partfun1(u1_struct_0(X1),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),X2,esk7_0),X3)|v2_struct_0(X1)|X4!=k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3)|~r1_tmap_1(X1,esk3_0,X2,X3)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~m1_subset_1(X4,u1_struct_0(esk3_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_17]), c_0_20]), c_0_19]), c_0_22]), c_0_21]), c_0_23]), c_0_24])]), c_0_26]), c_0_25]), c_0_30])).
% 0.14/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_38, plain, (v1_xboole_0(X1)|m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.14/0.37  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_12]), c_0_13])]), c_0_14])).
% 0.14/0.37  cnf(c_0_40, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),X1)|X2!=k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)|~r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)|~m1_subset_1(X2,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_12]), c_0_13]), c_0_36]), c_0_37])]), c_0_14])).
% 0.14/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1),u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_36]), c_0_37])]), c_0_39])).
% 0.14/0.37  cnf(c_0_42, negated_conjecture, (~r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_43, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,k1_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0),X1)|~r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])).
% 0.14/0.37  cnf(c_0_44, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,esk6_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.14/0.37  cnf(c_0_46, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])]), ['proof']).
% 0.14/0.37  # SZS output end CNFRefutation
% 0.14/0.37  # Proof object total steps             : 47
% 0.14/0.37  # Proof object clause steps            : 34
% 0.14/0.37  # Proof object formula steps           : 13
% 0.14/0.37  # Proof object conjectures             : 31
% 0.14/0.37  # Proof object clause conjectures      : 28
% 0.14/0.37  # Proof object formula conjectures     : 3
% 0.14/0.37  # Proof object initial clauses used    : 25
% 0.14/0.37  # Proof object initial formulas used   : 6
% 0.14/0.37  # Proof object generating inferences   : 9
% 0.14/0.37  # Proof object simplifying inferences  : 41
% 0.14/0.37  # Training examples: 0 positive, 0 negative
% 0.14/0.37  # Parsed axioms                        : 6
% 0.14/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.37  # Initial clauses                      : 28
% 0.14/0.37  # Removed in clause preprocessing      : 0
% 0.14/0.37  # Initial clauses in saturation        : 28
% 0.14/0.37  # Processed clauses                    : 79
% 0.14/0.37  # ...of these trivial                  : 0
% 0.14/0.37  # ...subsumed                          : 0
% 0.14/0.37  # ...remaining for further processing  : 79
% 0.14/0.37  # Other redundant clauses eliminated   : 0
% 0.14/0.37  # Clauses deleted for lack of memory   : 0
% 0.14/0.37  # Backward-subsumed                    : 1
% 0.14/0.37  # Backward-rewritten                   : 0
% 0.14/0.37  # Generated clauses                    : 28
% 0.14/0.37  # ...of the previous two non-trivial   : 24
% 0.14/0.37  # Contextual simplify-reflections      : 2
% 0.14/0.37  # Paramodulations                      : 27
% 0.14/0.37  # Factorizations                       : 0
% 0.14/0.37  # Equation resolutions                 : 1
% 0.14/0.37  # Propositional unsat checks           : 0
% 0.14/0.37  #    Propositional check models        : 0
% 0.14/0.37  #    Propositional check unsatisfiable : 0
% 0.14/0.37  #    Propositional clauses             : 0
% 0.14/0.37  #    Propositional clauses after purity: 0
% 0.14/0.37  #    Propositional unsat core size     : 0
% 0.14/0.37  #    Propositional preprocessing time  : 0.000
% 0.14/0.37  #    Propositional encoding time       : 0.000
% 0.14/0.37  #    Propositional solver time         : 0.000
% 0.14/0.37  #    Success case prop preproc time    : 0.000
% 0.14/0.37  #    Success case prop encoding time   : 0.000
% 0.14/0.37  #    Success case prop solver time     : 0.000
% 0.14/0.37  # Current number of processed clauses  : 50
% 0.14/0.37  #    Positive orientable unit clauses  : 21
% 0.14/0.37  #    Positive unorientable unit clauses: 0
% 0.14/0.37  #    Negative unit clauses             : 7
% 0.14/0.37  #    Non-unit-clauses                  : 22
% 0.14/0.37  # Current number of unprocessed clauses: 1
% 0.14/0.37  # ...number of literals in the above   : 12
% 0.14/0.37  # Current number of archived formulas  : 0
% 0.14/0.37  # Current number of archived clauses   : 29
% 0.14/0.37  # Clause-clause subsumption calls (NU) : 427
% 0.14/0.37  # Rec. Clause-clause subsumption calls : 20
% 0.14/0.37  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.37  # Unit Clause-clause subsumption calls : 14
% 0.14/0.37  # Rewrite failures with RHS unbound    : 0
% 0.14/0.37  # BW rewrite match attempts            : 0
% 0.14/0.37  # BW rewrite match successes           : 0
% 0.14/0.37  # Condensation attempts                : 0
% 0.14/0.37  # Condensation successes               : 0
% 0.14/0.37  # Termbank termtop insertions          : 4183
% 0.14/0.37  
% 0.14/0.37  # -------------------------------------------------
% 0.14/0.37  # User time                : 0.034 s
% 0.14/0.37  # System time              : 0.004 s
% 0.14/0.37  # Total time               : 0.037 s
% 0.14/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
