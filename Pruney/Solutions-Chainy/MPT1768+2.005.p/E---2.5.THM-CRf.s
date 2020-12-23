%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 781 expanded)
%              Number of clauses        :   54 ( 243 expanded)
%              Number of leaves         :    8 ( 190 expanded)
%              Depth                    :   12
%              Number of atoms          :  417 (9766 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t79_tmap_1,conjecture,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X5,X4) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tmap_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t78_tmap_1,axiom,(
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
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(c_0_8,negated_conjecture,(
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
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X4,X3)
                            & m1_pre_topc(X5,X4) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t79_tmap_1])).

fof(c_0_9,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( ( v1_funct_1(k3_tmap_1(X20,X21,X22,X23,X24))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))) )
      & ( v1_funct_2(k3_tmap_1(X20,X21,X22,X23,X24),u1_struct_0(X23),u1_struct_0(X21))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))) )
      & ( m1_subset_1(k3_tmap_1(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | ~ m1_pre_topc(X22,X20)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk4_0,esk3_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X15)
      | ~ m1_pre_topc(X18,X15)
      | ~ v1_funct_1(X19)
      | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X16))
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))
      | ~ m1_pre_topc(X18,X17)
      | k3_tmap_1(X15,X16,X17,X18,X19) = k2_partfun1(u1_struct_0(X17),u1_struct_0(X16),X19,u1_struct_0(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_12,plain,(
    ! [X30,X31,X32] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | ~ m1_pre_topc(X32,X31)
      | m1_pre_topc(X32,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X7,X8] :
      ( ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X8,X7)
      | v2_pre_topc(X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_25,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_33,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,esk6_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,esk6_0),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_28])])).

cnf(c_0_45,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk3_0,X2,esk6_0)) = k2_partfun1(u1_struct_0(X2),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,X2,esk6_0),u1_struct_0(X3))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_37]),c_0_17]),c_0_18])]),c_0_19]),c_0_38]),c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_47,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X25)
      | v2_struct_0(X28)
      | ~ m1_pre_topc(X28,X25)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))
      | ~ m1_pre_topc(X27,X28)
      | r2_funct_2(u1_struct_0(X27),u1_struct_0(X26),k3_tmap_1(X25,X26,X28,X27,k2_tmap_1(X25,X26,X29,X28)),k2_tmap_1(X25,X26,X29,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).

fof(c_0_48,plain,(
    ! [X11,X12,X13,X14] :
      ( v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ v1_funct_1(X13)
      | ~ v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))
      | ~ m1_pre_topc(X14,X11)
      | k2_tmap_1(X11,X12,X13,X14) = k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),X13,u1_struct_0(X14)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_41]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_55,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,esk6_0) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),u1_struct_0(esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_34])).

cnf(c_0_58,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X3,X2,X5,X4)),k2_tmap_1(X3,X2,X5,X1))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_52,c_0_23])).

cnf(c_0_59,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0) = k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_14]),c_0_15]),c_0_16]),c_0_41]),c_0_17]),c_0_44]),c_0_18]),c_0_43])]),c_0_19]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0)) = k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),u1_struct_0(esk5_0)) = k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_44]),c_0_43])]),c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_14]),c_0_15]),c_0_16]),c_0_41]),c_0_17]),c_0_44]),c_0_18]),c_0_43])]),c_0_60]),c_0_19]),c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0) = k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_61]),c_0_14]),c_0_15]),c_0_16]),c_0_50]),c_0_17]),c_0_44]),c_0_18]),c_0_43])]),c_0_19]),c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_66,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_57,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_64]),c_0_65])).

cnf(c_0_68,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_46]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.54  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.19/0.54  # and selection function PSelectComplexExceptRRHorn.
% 0.19/0.54  #
% 0.19/0.54  # Preprocessing time       : 0.028 s
% 0.19/0.54  # Presaturation interreduction done
% 0.19/0.54  
% 0.19/0.54  # Proof found!
% 0.19/0.54  # SZS status Theorem
% 0.19/0.54  # SZS output start CNFRefutation
% 0.19/0.54  fof(t79_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_tmap_1)).
% 0.19/0.54  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.19/0.54  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.19/0.54  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.19/0.54  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.54  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.54  fof(t78_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.19/0.54  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.54  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>((m1_pre_topc(X4,X3)&m1_pre_topc(X5,X4))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)))))))))), inference(assume_negation,[status(cth)],[t79_tmap_1])).
% 0.19/0.54  fof(c_0_9, plain, ![X20, X21, X22, X23, X24]:(((v1_funct_1(k3_tmap_1(X20,X21,X22,X23,X24))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X23,X20)|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))))&(v1_funct_2(k3_tmap_1(X20,X21,X22,X23,X24),u1_struct_0(X23),u1_struct_0(X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X23,X20)|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21)))))))&(m1_subset_1(k3_tmap_1(X20,X21,X22,X23,X24),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X21))))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_pre_topc(X22,X20)|~m1_pre_topc(X23,X20)|~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.19/0.54  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&((m1_pre_topc(esk4_0,esk3_0)&m1_pre_topc(esk5_0,esk4_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.19/0.54  fof(c_0_11, plain, ![X15, X16, X17, X18, X19]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_pre_topc(X17,X15)|(~m1_pre_topc(X18,X15)|(~v1_funct_1(X19)|~v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X16))|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16))))|(~m1_pre_topc(X18,X17)|k3_tmap_1(X15,X16,X17,X18,X19)=k2_partfun1(u1_struct_0(X17),u1_struct_0(X16),X19,u1_struct_0(X18)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.19/0.54  fof(c_0_12, plain, ![X30, X31, X32]:(~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|(~m1_pre_topc(X32,X31)|m1_pre_topc(X32,X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.19/0.54  cnf(c_0_13, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.54  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_20, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.54  cnf(c_0_21, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.54  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.54  cnf(c_0_23, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.54  fof(c_0_24, plain, ![X7, X8]:(~v2_pre_topc(X7)|~l1_pre_topc(X7)|(~m1_pre_topc(X8,X7)|v2_pre_topc(X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.54  fof(c_0_25, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.54  cnf(c_0_26, negated_conjecture, (m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.54  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_31, negated_conjecture, (v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.54  cnf(c_0_32, negated_conjecture, (v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk2_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.54  cnf(c_0_33, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.54  cnf(c_0_34, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_35, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.54  cnf(c_0_36, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.54  cnf(c_0_37, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.54  cnf(c_0_38, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,esk6_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.54  cnf(c_0_39, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,esk6_0),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.54  cnf(c_0_40, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.19/0.54  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_42, negated_conjecture, (m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 0.19/0.54  cnf(c_0_43, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_27]), c_0_28]), c_0_29])])).
% 0.19/0.54  cnf(c_0_44, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_28])])).
% 0.19/0.54  cnf(c_0_45, negated_conjecture, (k3_tmap_1(X1,esk2_0,X2,X3,k3_tmap_1(esk1_0,esk2_0,esk3_0,X2,esk6_0))=k2_partfun1(u1_struct_0(X2),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,X2,esk6_0),u1_struct_0(X3))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_37]), c_0_17]), c_0_18])]), c_0_19]), c_0_38]), c_0_39])).
% 0.19/0.54  cnf(c_0_46, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  fof(c_0_47, plain, ![X25, X26, X27, X28, X29]:(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X25)|(v2_struct_0(X28)|~m1_pre_topc(X28,X25)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X25),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X26))))|(~m1_pre_topc(X27,X28)|r2_funct_2(u1_struct_0(X27),u1_struct_0(X26),k3_tmap_1(X25,X26,X28,X27,k2_tmap_1(X25,X26,X29,X28)),k2_tmap_1(X25,X26,X29,X27)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).
% 0.19/0.54  fof(c_0_48, plain, ![X11, X12, X13, X14]:(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~v1_funct_1(X13)|~v1_funct_2(X13,u1_struct_0(X11),u1_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),u1_struct_0(X12))))|(~m1_pre_topc(X14,X11)|k2_tmap_1(X11,X12,X13,X14)=k2_partfun1(u1_struct_0(X11),u1_struct_0(X12),X13,u1_struct_0(X14)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.54  cnf(c_0_49, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.54  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_41]), c_0_44])])).
% 0.19/0.54  cnf(c_0_51, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.54  cnf(c_0_52, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.54  cnf(c_0_53, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.54  cnf(c_0_54, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk4_0))=k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.54  cnf(c_0_55, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_56, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,esk6_0)=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_50])).
% 0.19/0.54  cnf(c_0_57, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),u1_struct_0(esk5_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_51, c_0_34])).
% 0.19/0.54  cnf(c_0_58, plain, (r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X3,X2,X5,X4)),k2_tmap_1(X3,X2,X5,X1))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|v2_struct_0(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X4)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_52, c_0_23])).
% 0.19/0.54  cnf(c_0_59, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk6_0,esk4_0)=k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_14]), c_0_15]), c_0_16]), c_0_41]), c_0_17]), c_0_44]), c_0_18]), c_0_43])]), c_0_19]), c_0_55])).
% 0.19/0.54  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_61, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,u1_struct_0(esk5_0))=k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.54  cnf(c_0_62, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0),u1_struct_0(esk5_0))=k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_41]), c_0_44]), c_0_43])]), c_0_55])).
% 0.19/0.54  cnf(c_0_63, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,X1,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k2_tmap_1(esk3_0,esk2_0,esk6_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_14]), c_0_15]), c_0_16]), c_0_41]), c_0_17]), c_0_44]), c_0_18]), c_0_43])]), c_0_60]), c_0_19]), c_0_55])).
% 0.19/0.54  cnf(c_0_64, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk6_0,esk5_0)=k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_61]), c_0_14]), c_0_15]), c_0_16]), c_0_50]), c_0_17]), c_0_44]), c_0_18]), c_0_43])]), c_0_19]), c_0_55])).
% 0.19/0.54  cnf(c_0_65, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_66, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))=k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_57, c_0_62])).
% 0.19/0.54  cnf(c_0_67, negated_conjecture, (r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_64]), c_0_65])).
% 0.19/0.54  cnf(c_0_68, negated_conjecture, (k3_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))=k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_46]), c_0_28]), c_0_29])]), c_0_30])).
% 0.19/0.54  cnf(c_0_69, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,esk6_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.54  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68]), c_0_69]), ['proof']).
% 0.19/0.54  # SZS output end CNFRefutation
% 0.19/0.54  # Proof object total steps             : 71
% 0.19/0.54  # Proof object clause steps            : 54
% 0.19/0.54  # Proof object formula steps           : 17
% 0.19/0.54  # Proof object conjectures             : 46
% 0.19/0.54  # Proof object clause conjectures      : 43
% 0.19/0.54  # Proof object formula conjectures     : 3
% 0.19/0.54  # Proof object initial clauses used    : 26
% 0.19/0.54  # Proof object initial formulas used   : 8
% 0.19/0.54  # Proof object generating inferences   : 24
% 0.19/0.54  # Proof object simplifying inferences  : 107
% 0.19/0.54  # Training examples: 0 positive, 0 negative
% 0.19/0.54  # Parsed axioms                        : 8
% 0.19/0.54  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.54  # Initial clauses                      : 27
% 0.19/0.54  # Removed in clause preprocessing      : 0
% 0.19/0.54  # Initial clauses in saturation        : 27
% 0.19/0.54  # Processed clauses                    : 1494
% 0.19/0.54  # ...of these trivial                  : 8
% 0.19/0.54  # ...subsumed                          : 769
% 0.19/0.54  # ...remaining for further processing  : 717
% 0.19/0.54  # Other redundant clauses eliminated   : 0
% 0.19/0.54  # Clauses deleted for lack of memory   : 0
% 0.19/0.54  # Backward-subsumed                    : 2
% 0.19/0.54  # Backward-rewritten                   : 8
% 0.19/0.54  # Generated clauses                    : 2097
% 0.19/0.54  # ...of the previous two non-trivial   : 1940
% 0.19/0.54  # Contextual simplify-reflections      : 155
% 0.19/0.54  # Paramodulations                      : 2097
% 0.19/0.54  # Factorizations                       : 0
% 0.19/0.54  # Equation resolutions                 : 0
% 0.19/0.54  # Propositional unsat checks           : 0
% 0.19/0.54  #    Propositional check models        : 0
% 0.19/0.54  #    Propositional check unsatisfiable : 0
% 0.19/0.54  #    Propositional clauses             : 0
% 0.19/0.54  #    Propositional clauses after purity: 0
% 0.19/0.54  #    Propositional unsat core size     : 0
% 0.19/0.54  #    Propositional preprocessing time  : 0.000
% 0.19/0.54  #    Propositional encoding time       : 0.000
% 0.19/0.54  #    Propositional solver time         : 0.000
% 0.19/0.54  #    Success case prop preproc time    : 0.000
% 0.19/0.54  #    Success case prop encoding time   : 0.000
% 0.19/0.54  #    Success case prop solver time     : 0.000
% 0.19/0.54  # Current number of processed clauses  : 680
% 0.19/0.54  #    Positive orientable unit clauses  : 24
% 0.19/0.54  #    Positive unorientable unit clauses: 0
% 0.19/0.54  #    Negative unit clauses             : 6
% 0.19/0.54  #    Non-unit-clauses                  : 650
% 0.19/0.54  # Current number of unprocessed clauses: 488
% 0.19/0.54  # ...number of literals in the above   : 4738
% 0.19/0.54  # Current number of archived formulas  : 0
% 0.19/0.54  # Current number of archived clauses   : 37
% 0.19/0.54  # Clause-clause subsumption calls (NU) : 156569
% 0.19/0.54  # Rec. Clause-clause subsumption calls : 21998
% 0.19/0.54  # Non-unit clause-clause subsumptions  : 926
% 0.19/0.54  # Unit Clause-clause subsumption calls : 33
% 0.19/0.54  # Rewrite failures with RHS unbound    : 0
% 0.19/0.54  # BW rewrite match attempts            : 53
% 0.19/0.54  # BW rewrite match successes           : 4
% 0.19/0.54  # Condensation attempts                : 0
% 0.19/0.54  # Condensation successes               : 0
% 0.19/0.54  # Termbank termtop insertions          : 98185
% 0.19/0.54  
% 0.19/0.54  # -------------------------------------------------
% 0.19/0.54  # User time                : 0.195 s
% 0.19/0.54  # System time              : 0.009 s
% 0.19/0.54  # Total time               : 0.204 s
% 0.19/0.54  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
