%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1771+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:43 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 450 expanded)
%              Number of clauses        :   62 ( 145 expanded)
%              Number of leaves         :    8 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  566 (5745 expanded)
%              Number of equality atoms :   16 ( 251 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   36 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t82_tmap_1,conjecture,(
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
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6) )
                                 => r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t81_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( X6 = X7
                                  & m1_pre_topc(X4,X3)
                                  & r1_tmap_1(X3,X2,X5,X6) )
                               => r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6) )
                                   => r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t82_tmap_1])).

fof(c_0_9,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ m1_pre_topc(X34,X32)
      | v2_struct_0(X35)
      | ~ m1_pre_topc(X35,X32)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X32),u1_struct_0(X33))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
      | ~ m1_pre_topc(X34,X35)
      | r2_funct_2(u1_struct_0(X34),u1_struct_0(X33),k3_tmap_1(X32,X33,X35,X34,k2_tmap_1(X32,X33,X36,X35)),k2_tmap_1(X32,X33,X36,X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t78_tmap_1])])])])).

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
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk3_0))
    & esk6_0 = esk7_0
    & r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0)
    & ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
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

fof(c_0_12,plain,(
    ! [X16,X17,X18,X19] :
      ( ( v1_funct_1(k2_tmap_1(X16,X17,X18,X19))
        | ~ l1_struct_0(X16)
        | ~ l1_struct_0(X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_struct_0(X19) )
      & ( v1_funct_2(k2_tmap_1(X16,X17,X18,X19),u1_struct_0(X19),u1_struct_0(X17))
        | ~ l1_struct_0(X16)
        | ~ l1_struct_0(X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_struct_0(X19) )
      & ( m1_subset_1(k2_tmap_1(X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X17))))
        | ~ l1_struct_0(X16)
        | ~ l1_struct_0(X17)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
        | ~ l1_struct_0(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

fof(c_0_13,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | l1_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_14,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ r2_funct_2(X28,X29,X30,X31)
        | X30 = X31
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( X30 != X31
        | r2_funct_2(X28,X29,X30,X31)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X28,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X28,X29)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_30,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,X2,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_22]),c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X5,X2,X6,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk2_0,X2,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_41,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X5,X2,X6,X3)),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,plain,
    ( X1 = k2_tmap_1(X2,X3,X4,X5)
    | ~ r2_funct_2(u1_struct_0(X5),u1_struct_0(X3),X1,k2_tmap_1(X2,X3,X4,X5))
    | ~ l1_struct_0(X5)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X5),u1_struct_0(X3))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk2_0,X2,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_19])])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk2_0,X2,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)),u1_struct_0(X3),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_47,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X5,X2,X6,X3)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X5)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

fof(c_0_48,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | v2_struct_0(X39)
      | ~ m1_pre_topc(X39,X37)
      | v2_struct_0(X40)
      | ~ m1_pre_topc(X40,X37)
      | ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,u1_struct_0(X39),u1_struct_0(X38))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))
      | ~ m1_subset_1(X42,u1_struct_0(X39))
      | ~ m1_subset_1(X43,u1_struct_0(X40))
      | X42 != X43
      | ~ m1_pre_topc(X40,X39)
      | ~ r1_tmap_1(X39,X38,X41,X42)
      | r1_tmap_1(X40,X38,k3_tmap_1(X37,X38,X39,X40,X41),X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,X1,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_37]),c_0_19]),c_0_21])]),c_0_23])).

cnf(c_0_51,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk2_0,X2,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)),u1_struct_0(X3),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_19])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk2_0,X2,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_20])]),c_0_22])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | X6 != X7
    | ~ m1_pre_topc(X4,X3)
    | ~ r1_tmap_1(X3,X2,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0)
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,X1,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_37]),c_0_19]),c_0_21])]),c_0_23])).

cnf(c_0_56,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk2_0,X2,X3,k2_tmap_1(esk1_0,esk2_0,esk5_0,X2)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_28]),c_0_19])])).

cnf(c_0_57,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0)
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_31])])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,X1,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)))
    | ~ l1_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_37]),c_0_19]),c_0_21])]),c_0_23])).

cnf(c_0_60,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,k2_tmap_1(X5,X2,X6,X4)),X7)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,k2_tmap_1(X5,X2,X6,X4),X7)
    | ~ l1_struct_0(X4)
    | ~ l1_struct_0(X5)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ v1_funct_2(X6,u1_struct_0(X5),u1_struct_0(X2))
    | ~ v1_funct_1(X6)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_25]),c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_61,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_31])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_65,plain,(
    ! [X26,X27] :
      ( ~ l1_pre_topc(X26)
      | ~ m1_pre_topc(X27,X26)
      | l1_pre_topc(X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),X1)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X1)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_38]),c_0_37]),c_0_31]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_39]),c_0_32]),c_0_22]),c_0_23])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_71,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_31]),c_0_19])])).

cnf(c_0_74,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk3_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_28]),c_0_73])])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_37]),c_0_19])])).

cnf(c_0_76,negated_conjecture,
    ( ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_28]),c_0_75])])).

cnf(c_0_77,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_28]),c_0_18])])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_28]),c_0_19])]),
    [proof]).

%------------------------------------------------------------------------------
