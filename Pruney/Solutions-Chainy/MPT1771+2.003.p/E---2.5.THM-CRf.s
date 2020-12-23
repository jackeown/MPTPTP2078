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
% DateTime   : Thu Dec  3 11:17:45 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 (6654 expanded)
%              Number of clauses        :   75 (2028 expanded)
%              Number of leaves         :   11 (1636 expanded)
%              Depth                    :   15
%              Number of atoms          :  584 (87147 expanded)
%              Number of equality atoms :   36 (4526 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   36 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t77_tmap_1,axiom,(
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
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))
                              & m1_pre_topc(X4,X3) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t64_tmap_1,axiom,(
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
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,plain,(
    ! [X20,X21,X22,X23,X24] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X20)
      | ~ m1_pre_topc(X23,X20)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))
      | ~ m1_pre_topc(X23,X22)
      | k3_tmap_1(X20,X21,X22,X23,X24) = k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),X24,u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_13,plain,(
    ! [X43,X44,X45] :
      ( ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | ~ m1_pre_topc(X44,X43)
      | ~ m1_pre_topc(X45,X44)
      | m1_pre_topc(X45,X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_14,plain,(
    ! [X25,X26,X27,X28,X29] :
      ( ( v1_funct_1(k3_tmap_1(X25,X26,X27,X28,X29))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_pre_topc(X28,X25)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))) )
      & ( v1_funct_2(k3_tmap_1(X25,X26,X27,X28,X29),u1_struct_0(X28),u1_struct_0(X26))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_pre_topc(X28,X25)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))) )
      & ( m1_subset_1(k3_tmap_1(X25,X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_pre_topc(X27,X25)
        | ~ m1_pre_topc(X28,X25)
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_16,plain,(
    ! [X30] :
      ( ~ l1_pre_topc(X30)
      | m1_pre_topc(X30,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_31,plain,(
    ! [X16,X17,X18,X19] :
      ( v2_struct_0(X16)
      | ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))
      | ~ m1_pre_topc(X19,X16)
      | k2_tmap_1(X16,X17,X18,X19) = k2_partfun1(u1_struct_0(X16),u1_struct_0(X17),X18,u1_struct_0(X19)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_32,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_37,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

fof(c_0_38,plain,(
    ! [X14,X15] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | l1_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_39,plain,(
    ! [X12,X13] :
      ( ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_pre_topc(X13,X12)
      | v2_pre_topc(X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_40,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_33]),c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_46,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X2)) = k2_tmap_1(X1,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_21]),c_0_22])]),c_0_25]),c_0_44]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_41]),c_0_27])])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_27]),c_0_34])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_33]),c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_41]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_53]),c_0_41]),c_0_21]),c_0_27]),c_0_22]),c_0_34]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_35])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_57,plain,(
    ! [X37,X38,X39,X40,X41,X42] :
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
      | ~ v1_funct_2(X41,u1_struct_0(X37),u1_struct_0(X38))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,u1_struct_0(X39),u1_struct_0(X38))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))
      | ~ r2_funct_2(u1_struct_0(X39),u1_struct_0(X38),X42,k2_tmap_1(X37,X38,X41,X39))
      | ~ m1_pre_topc(X40,X39)
      | r2_funct_2(u1_struct_0(X40),u1_struct_0(X38),k3_tmap_1(X37,X38,X39,X40,X42),k2_tmap_1(X37,X38,X41,X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_tmap_1])])])])).

fof(c_0_58,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X8,X9,X10,X11)
        | X10 = X11
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != X11
        | r2_funct_2(X8,X9,X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X8,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X11)
        | ~ v1_funct_2(X11,X8,X9)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_55]),c_0_41]),c_0_33]),c_0_21]),c_0_27]),c_0_22]),c_0_34]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_35])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_55]),c_0_41]),c_0_33]),c_0_21]),c_0_27]),c_0_22]),c_0_34]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_35])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_55]),c_0_41]),c_0_33]),c_0_21]),c_0_27]),c_0_22]),c_0_34]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_35])).

cnf(c_0_63,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_56])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_59]),c_0_21]),c_0_22]),c_0_60]),c_0_61]),c_0_62])]),c_0_25])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_68,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_33]),c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X5),k2_tmap_1(X1,X2,X6,X4))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X5,k2_tmap_1(X1,X2,X6,X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X6) ),
    inference(csr,[status(thm)],[c_0_64,c_0_18])).

cnf(c_0_71,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_50])).

fof(c_0_74,plain,(
    ! [X31,X32,X33,X34,X35,X36] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,u1_struct_0(X32),u1_struct_0(X31))
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
      | v2_struct_0(X34)
      | ~ m1_pre_topc(X34,X32)
      | ~ m1_subset_1(X35,u1_struct_0(X32))
      | ~ m1_subset_1(X36,u1_struct_0(X34))
      | X35 != X36
      | ~ r1_tmap_1(X32,X31,X33,X35)
      | r1_tmap_1(X34,X31,k2_tmap_1(X32,X31,X33,X34),X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_76,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_69]),c_0_56]),c_0_21]),c_0_27]),c_0_22]),c_0_34]),c_0_20]),c_0_23]),c_0_24])]),c_0_25]),c_0_35])).

cnf(c_0_77,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3)),k2_tmap_1(X1,X2,X5,X4))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k2_tmap_1(X1,X2,X5,X3))
    | ~ v1_funct_1(X5) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_41]),c_0_27]),c_0_34])]),c_0_35])).

cnf(c_0_79,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) = k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_81,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_56])])).

cnf(c_0_83,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_67]),c_0_41]),c_0_21]),c_0_27]),c_0_22]),c_0_34]),c_0_60]),c_0_20]),c_0_61]),c_0_23]),c_0_62]),c_0_24])]),c_0_35]),c_0_25]),c_0_52]),c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_80]),c_0_67]),c_0_73]),c_0_21]),c_0_50]),c_0_22]),c_0_51]),c_0_60]),c_0_61]),c_0_62])]),c_0_25]),c_0_52])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_80]),c_0_67]),c_0_73]),c_0_21]),c_0_50]),c_0_22]),c_0_51]),c_0_60]),c_0_61]),c_0_62])]),c_0_25]),c_0_52])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_80]),c_0_67]),c_0_73]),c_0_21]),c_0_50]),c_0_22]),c_0_51]),c_0_60]),c_0_61]),c_0_62])]),c_0_25]),c_0_52])).

cnf(c_0_87,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_85]),c_0_86])])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_90,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_91,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_92,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),X1)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_67]),c_0_50]),c_0_21]),c_0_51]),c_0_22]),c_0_60]),c_0_61]),c_0_62])]),c_0_25]),c_0_52]),c_0_79])).

cnf(c_0_93,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_91,c_0_90])).

cnf(c_0_97,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94]),c_0_95])]),c_0_96]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:19:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.41  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.029 s
% 0.20/0.41  # Presaturation interreduction done
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(t82_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6))=>r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_tmap_1)).
% 0.20/0.41  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.41  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.41  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.20/0.41  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.41  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.41  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.41  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.41  fof(t77_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))&m1_pre_topc(X4,X3))=>r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 0.20/0.41  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.20/0.41  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.20/0.41  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X5,X4),X6))=>r1_tmap_1(X3,X2,k2_tmap_1(X1,X2,X5,X3),X7))))))))))), inference(assume_negation,[status(cth)],[t82_tmap_1])).
% 0.20/0.41  fof(c_0_12, plain, ![X20, X21, X22, X23, X24]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_pre_topc(X22,X20)|(~m1_pre_topc(X23,X20)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))|(~m1_pre_topc(X23,X22)|k3_tmap_1(X20,X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),X24,u1_struct_0(X23)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.41  fof(c_0_13, plain, ![X43, X44, X45]:(~v2_pre_topc(X43)|~l1_pre_topc(X43)|(~m1_pre_topc(X44,X43)|(~m1_pre_topc(X45,X44)|m1_pre_topc(X45,X43)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X25, X26, X27, X28, X29]:(((v1_funct_1(k3_tmap_1(X25,X26,X27,X28,X29))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X25)|~m1_pre_topc(X28,X25)|~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))))&(v1_funct_2(k3_tmap_1(X25,X26,X27,X28,X29),u1_struct_0(X28),u1_struct_0(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X25)|~m1_pre_topc(X28,X25)|~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26)))))))&(m1_subset_1(k3_tmap_1(X25,X26,X27,X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X26))))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_pre_topc(X27,X25)|~m1_pre_topc(X28,X25)|~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X26))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.20/0.41  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&(m1_subset_1(esk7_0,u1_struct_0(esk3_0))&((esk6_0=esk7_0&r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0))&~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.20/0.41  fof(c_0_16, plain, ![X30]:(~l1_pre_topc(X30)|m1_pre_topc(X30,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.41  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_18, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_19, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_26, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.41  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_28, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_29, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_30, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.20/0.41  fof(c_0_31, plain, ![X16, X17, X18, X19]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))|(~m1_pre_topc(X19,X16)|k2_tmap_1(X16,X17,X18,X19)=k2_partfun1(u1_struct_0(X16),u1_struct_0(X17),X18,u1_struct_0(X19)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.41  cnf(c_0_32, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.41  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.41  cnf(c_0_34, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_36, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.41  cnf(c_0_37, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.41  fof(c_0_38, plain, ![X14, X15]:(~l1_pre_topc(X14)|(~m1_pre_topc(X15,X14)|l1_pre_topc(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.41  fof(c_0_39, plain, ![X12, X13]:(~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_pre_topc(X13,X12)|v2_pre_topc(X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.41  cnf(c_0_43, negated_conjecture, (m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.41  cnf(c_0_44, negated_conjecture, (v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_33]), c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.41  cnf(c_0_45, negated_conjecture, (v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.41  cnf(c_0_46, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_47, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),u1_struct_0(X2))=k2_tmap_1(X1,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),X2)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_21]), c_0_22])]), c_0_25]), c_0_44]), c_0_45])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_41]), c_0_27])])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_27]), c_0_34])])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_53, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_33]), c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.41  cnf(c_0_54, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),u1_struct_0(X1))=k2_tmap_1(esk4_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_41]), c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.41  cnf(c_0_55, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_53]), c_0_41]), c_0_21]), c_0_27]), c_0_22]), c_0_34]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_35])).
% 0.20/0.41  cnf(c_0_56, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  fof(c_0_57, plain, ![X37, X38, X39, X40, X41, X42]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(v2_struct_0(X39)|~m1_pre_topc(X39,X37)|(v2_struct_0(X40)|~m1_pre_topc(X40,X37)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X39),u1_struct_0(X38))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X39),u1_struct_0(X38))))|(~r2_funct_2(u1_struct_0(X39),u1_struct_0(X38),X42,k2_tmap_1(X37,X38,X41,X39))|~m1_pre_topc(X40,X39)|r2_funct_2(u1_struct_0(X40),u1_struct_0(X38),k3_tmap_1(X37,X38,X39,X40,X42),k2_tmap_1(X37,X38,X41,X40))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_tmap_1])])])])).
% 0.20/0.41  fof(c_0_58, plain, ![X8, X9, X10, X11]:((~r2_funct_2(X8,X9,X10,X11)|X10=X11|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))&(X10!=X11|r2_funct_2(X8,X9,X10,X11)|(~v1_funct_1(X10)|~v1_funct_2(X10,X8,X9)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|~v1_funct_1(X11)|~v1_funct_2(X11,X8,X9)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(X1))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X1)|~m1_pre_topc(X1,esk4_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55]), c_0_55])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_55]), c_0_41]), c_0_33]), c_0_21]), c_0_27]), c_0_22]), c_0_34]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_35])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_55]), c_0_41]), c_0_33]), c_0_21]), c_0_27]), c_0_22]), c_0_34]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_35])).
% 0.20/0.41  cnf(c_0_62, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_55]), c_0_41]), c_0_33]), c_0_21]), c_0_27]), c_0_22]), c_0_34]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_35])).
% 0.20/0.41  cnf(c_0_63, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_40, c_0_56])).
% 0.20/0.41  cnf(c_0_64, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.20/0.41  cnf(c_0_65, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X2)|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_59]), c_0_21]), c_0_22]), c_0_60]), c_0_61]), c_0_62])]), c_0_25])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_68, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.41  cnf(c_0_69, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_33]), c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.41  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X5),k2_tmap_1(X1,X2,X6,X4))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X5,k2_tmap_1(X1,X2,X6,X3))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X5)|~v1_funct_1(X6)), inference(csr,[status(thm)],[c_0_64, c_0_18])).
% 0.20/0.41  cnf(c_0_71, plain, (r2_funct_2(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_65])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_50])).
% 0.20/0.41  fof(c_0_74, plain, ![X31, X32, X33, X34, X35, X36]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|(v2_struct_0(X34)|~m1_pre_topc(X34,X32)|(~m1_subset_1(X35,u1_struct_0(X32))|(~m1_subset_1(X36,u1_struct_0(X34))|(X35!=X36|~r1_tmap_1(X32,X31,X33,X35)|r1_tmap_1(X34,X31,k2_tmap_1(X32,X31,X33,X34),X36)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (X1=k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0)|~m1_pre_topc(X2,esk1_0)|~r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),X1,k3_tmap_1(esk1_0,esk2_0,esk1_0,X2,esk5_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_43]), c_0_44]), c_0_45])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_69]), c_0_56]), c_0_21]), c_0_27]), c_0_22]), c_0_34]), c_0_20]), c_0_23]), c_0_24])]), c_0_25]), c_0_35])).
% 0.20/0.41  cnf(c_0_77, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,k2_tmap_1(X1,X2,X5,X3)),k2_tmap_1(X1,X2,X5,X4))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(k2_tmap_1(X1,X2,X5,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_2(k2_tmap_1(X1,X2,X5,X3),u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(k2_tmap_1(X1,X2,X5,X3))|~v1_funct_1(X5)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_41]), c_0_27]), c_0_34])]), c_0_35])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (k3_tmap_1(esk4_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))=k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_50]), c_0_51])]), c_0_52])).
% 0.20/0.41  cnf(c_0_81, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (X1=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_56])])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_67]), c_0_41]), c_0_21]), c_0_27]), c_0_22]), c_0_34]), c_0_60]), c_0_20]), c_0_61]), c_0_23]), c_0_62]), c_0_24])]), c_0_35]), c_0_25]), c_0_52]), c_0_79])).
% 0.20/0.41  cnf(c_0_84, negated_conjecture, (m1_subset_1(k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_80]), c_0_67]), c_0_73]), c_0_21]), c_0_50]), c_0_22]), c_0_51]), c_0_60]), c_0_61]), c_0_62])]), c_0_25]), c_0_52])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (v1_funct_2(k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_80]), c_0_67]), c_0_73]), c_0_21]), c_0_50]), c_0_22]), c_0_51]), c_0_60]), c_0_61]), c_0_62])]), c_0_25]), c_0_52])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (v1_funct_1(k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_80]), c_0_67]), c_0_73]), c_0_21]), c_0_50]), c_0_22]), c_0_51]), c_0_60]), c_0_61]), c_0_62])]), c_0_25]), c_0_52])).
% 0.20/0.41  cnf(c_0_87, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X3))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)), inference(er,[status(thm)],[c_0_81])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, (k2_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_85]), c_0_86])])).
% 0.20/0.41  cnf(c_0_89, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_90, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_91, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_92, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),X1)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_67]), c_0_50]), c_0_21]), c_0_51]), c_0_22]), c_0_60]), c_0_61]), c_0_62])]), c_0_25]), c_0_52]), c_0_79])).
% 0.20/0.41  cnf(c_0_93, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_94, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_89, c_0_90])).
% 0.20/0.41  cnf(c_0_95, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_96, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_91, c_0_90])).
% 0.20/0.41  cnf(c_0_97, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_94]), c_0_95])]), c_0_96]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 98
% 0.20/0.41  # Proof object clause steps            : 75
% 0.20/0.41  # Proof object formula steps           : 23
% 0.20/0.41  # Proof object conjectures             : 60
% 0.20/0.41  # Proof object clause conjectures      : 57
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 32
% 0.20/0.41  # Proof object initial formulas used   : 11
% 0.20/0.41  # Proof object generating inferences   : 36
% 0.20/0.41  # Proof object simplifying inferences  : 217
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 11
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 32
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 32
% 0.20/0.41  # Processed clauses                    : 273
% 0.20/0.41  # ...of these trivial                  : 27
% 0.20/0.41  # ...subsumed                          : 41
% 0.20/0.41  # ...remaining for further processing  : 205
% 0.20/0.41  # Other redundant clauses eliminated   : 2
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 0
% 0.20/0.41  # Backward-rewritten                   : 36
% 0.20/0.41  # Generated clauses                    : 410
% 0.20/0.41  # ...of the previous two non-trivial   : 307
% 0.20/0.41  # Contextual simplify-reflections      : 16
% 0.20/0.41  # Paramodulations                      : 408
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 2
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 135
% 0.20/0.41  #    Positive orientable unit clauses  : 44
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 5
% 0.20/0.41  #    Non-unit-clauses                  : 86
% 0.20/0.41  # Current number of unprocessed clauses: 89
% 0.20/0.41  # ...number of literals in the above   : 492
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 68
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 5430
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 1027
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 57
% 0.20/0.41  # Unit Clause-clause subsumption calls : 195
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 84
% 0.20/0.41  # BW rewrite match successes           : 7
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 25918
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.057 s
% 0.20/0.41  # System time              : 0.004 s
% 0.20/0.41  # Total time               : 0.061 s
% 0.20/0.41  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
