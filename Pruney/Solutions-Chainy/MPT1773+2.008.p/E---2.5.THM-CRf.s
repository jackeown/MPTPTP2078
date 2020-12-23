%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 823 expanded)
%              Number of clauses        :   54 ( 262 expanded)
%              Number of leaves         :    8 ( 198 expanded)
%              Depth                    :   12
%              Number of atoms          :  447 (12889 expanded)
%              Number of equality atoms :   21 ( 549 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t84_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X4)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

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

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t65_tmap_1,axiom,(
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
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( r1_tarski(X5,u1_struct_0(X4))
                                  & m1_connsp_2(X5,X2,X6)
                                  & X6 = X7 )
                               => ( r1_tmap_1(X2,X1,X3,X6)
                                <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

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
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X3))
                                     => ( ( v3_pre_topc(X6,X4)
                                          & r2_hidden(X7,X6)
                                          & r1_tarski(X6,u1_struct_0(X3))
                                          & X7 = X8 )
                                       => ( r1_tmap_1(X4,X2,X5,X7)
                                        <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t84_tmap_1])).

fof(c_0_9,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | l1_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

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
    & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk3_0))
    & v3_pre_topc(esk6_0,esk4_0)
    & r2_hidden(esk7_0,esk6_0)
    & r1_tarski(esk6_0,u1_struct_0(esk3_0))
    & esk7_0 = esk8_0
    & ( ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
      | ~ r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0) )
    & ( r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
      | r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

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
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | ~ m1_pre_topc(X34,X33)
      | m1_pre_topc(X34,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_14,plain,(
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

cnf(c_0_15,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
      | ~ m1_subset_1(X15,u1_struct_0(X13))
      | ~ v3_pre_topc(X14,X13)
      | ~ r2_hidden(X15,X14)
      | m1_connsp_2(X14,X13,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_21,plain,
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

cnf(c_0_22,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_16]),c_0_17]),c_0_19])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_33,plain,(
    ! [X25,X26,X27,X28,X29,X30,X31] :
      ( ( ~ r1_tmap_1(X26,X25,X27,X30)
        | r1_tmap_1(X28,X25,k2_tmap_1(X26,X25,X27,X28),X31)
        | ~ r1_tarski(X29,u1_struct_0(X28))
        | ~ m1_connsp_2(X29,X26,X30)
        | X30 != X31
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X26))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( ~ r1_tmap_1(X28,X25,k2_tmap_1(X26,X25,X27,X28),X31)
        | r1_tmap_1(X26,X25,X27,X30)
        | ~ r1_tarski(X29,u1_struct_0(X28))
        | ~ m1_connsp_2(X29,X26,X30)
        | X30 != X31
        | ~ m1_subset_1(X31,u1_struct_0(X28))
        | ~ m1_subset_1(X30,u1_struct_0(X26))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))
        | v2_struct_0(X28)
        | ~ m1_pre_topc(X28,X26)
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | v2_struct_0(X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_36,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_37,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ r1_tarski(X7,u1_struct_0(X1))
    | ~ m1_connsp_2(X7,X3,X6)
    | X6 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_connsp_2(esk6_0,X1,esk7_0)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(esk6_0,X1)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_29])]),c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ r1_tarski(X6,u1_struct_0(X5))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X6,X1,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( m1_connsp_2(esk6_0,esk4_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_28]),c_0_30])]),c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_49,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
    | r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk5_0) = k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_38]),c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,plain,
    ( r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ r1_tarski(X7,u1_struct_0(X5))
    | ~ m1_connsp_2(X7,X1,X4)
    | X4 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X5,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
    | ~ r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,X2,esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(esk4_0,X1,X2,X3),esk7_0)
    | ~ r1_tarski(esk6_0,u1_struct_0(X3))
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X3))
    | ~ m1_pre_topc(X3,esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_42]),c_0_43]),c_0_28]),c_0_30])]),c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0) = k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_16]),c_0_17]),c_0_19])]),c_0_52])).

cnf(c_0_61,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ r1_tarski(X6,u1_struct_0(X1))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_connsp_2(X6,X3,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,X2,esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57]),c_0_38])]),c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)
    | r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(X1,X2,k2_tmap_1(esk4_0,X2,X3,X1),esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk4_0,X2,X3,esk7_0)
    | ~ r1_tarski(esk6_0,u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_42]),c_0_43]),c_0_28]),c_0_30])]),c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_29])]),c_0_31]),c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk4_0,X1,X2,esk7_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_56]),c_0_57]),c_0_38])]),c_0_58])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_24]),c_0_67]),c_0_25]),c_0_26]),c_0_27]),c_0_29])]),c_0_69]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:28:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.12/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t84_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.12/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.12/0.37  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.12/0.37  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.12/0.37  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.12/0.37  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.12/0.37  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.12/0.37  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.12/0.37  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t84_tmap_1])).
% 0.12/0.37  fof(c_0_9, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.12/0.37  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk3_0))&((((v3_pre_topc(esk6_0,esk4_0)&r2_hidden(esk7_0,esk6_0))&r1_tarski(esk6_0,u1_struct_0(esk3_0)))&esk7_0=esk8_0)&((~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0))&(r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.12/0.37  fof(c_0_11, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|v2_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X20, X21, X22, X23, X24]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(~m1_pre_topc(X22,X20)|(~m1_pre_topc(X23,X20)|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X22),u1_struct_0(X21))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X21))))|(~m1_pre_topc(X23,X22)|k3_tmap_1(X20,X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X22),u1_struct_0(X21),X24,u1_struct_0(X23)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|(~m1_pre_topc(X34,X33)|m1_pre_topc(X34,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.12/0.37  fof(c_0_14, plain, ![X16, X17, X18, X19]:(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16)|(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X17))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X17))))|(~m1_pre_topc(X19,X16)|k2_tmap_1(X16,X17,X18,X19)=k2_partfun1(u1_struct_0(X16),u1_struct_0(X17),X18,u1_struct_0(X19)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.12/0.37  cnf(c_0_15, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_18, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_20, plain, ![X13, X14, X15]:(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))|(~m1_subset_1(X15,u1_struct_0(X13))|(~v3_pre_topc(X14,X13)|~r2_hidden(X15,X14)|m1_connsp_2(X14,X13,X15))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.12/0.37  cnf(c_0_21, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_22, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_23, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_16]), c_0_17]), c_0_19])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  fof(c_0_33, plain, ![X25, X26, X27, X28, X29, X30, X31]:((~r1_tmap_1(X26,X25,X27,X30)|r1_tmap_1(X28,X25,k2_tmap_1(X26,X25,X27,X28),X31)|(~r1_tarski(X29,u1_struct_0(X28))|~m1_connsp_2(X29,X26,X30)|X30!=X31)|~m1_subset_1(X31,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(~r1_tmap_1(X28,X25,k2_tmap_1(X26,X25,X27,X28),X31)|r1_tmap_1(X26,X25,X27,X30)|(~r1_tarski(X29,u1_struct_0(X28))|~m1_connsp_2(X29,X26,X30)|X30!=X31)|~m1_subset_1(X31,u1_struct_0(X28))|~m1_subset_1(X30,u1_struct_0(X26))|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X26)))|(v2_struct_0(X28)|~m1_pre_topc(X28,X26))|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25)))))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26))|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.12/0.37  cnf(c_0_34, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_36, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30])]), c_0_31]), c_0_32])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_39, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (m1_connsp_2(esk6_0,X1,esk7_0)|v2_struct_0(X1)|~v3_pre_topc(esk6_0,X1)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_29])]), c_0_31])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_46, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~r1_tarski(X6,u1_struct_0(X5))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X5))|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(er,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_47, negated_conjecture, (m1_connsp_2(esk6_0,esk4_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_28]), c_0_30])]), c_0_32])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk5_0)=k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_38]), c_0_45])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_53, plain, (r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)|v2_struct_0(X5)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,X3,X4)|~r1_tarski(X7,u1_struct_0(X5))|~m1_connsp_2(X7,X1,X4)|X4!=X6|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X5,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (r1_tmap_1(esk4_0,X1,X2,esk7_0)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_tmap_1(X3,X1,k2_tmap_1(esk4_0,X1,X2,X3),esk7_0)|~r1_tarski(esk6_0,u1_struct_0(X3))|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~m1_subset_1(esk7_0,u1_struct_0(X3))|~m1_pre_topc(X3,esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_42]), c_0_43]), c_0_28]), c_0_30])]), c_0_32])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.37  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)|r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_50, c_0_49])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0)=k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_16]), c_0_17]), c_0_19])]), c_0_52])).
% 0.12/0.37  cnf(c_0_61, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,X2,X4,X5)|~r1_tarski(X6,u1_struct_0(X1))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_connsp_2(X6,X3,X5)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X3))|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)), inference(er,[status(thm)],[c_0_53])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)|~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_54, c_0_49])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (r1_tmap_1(esk4_0,X1,X2,esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57]), c_0_38])]), c_0_58])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)|r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_59, c_0_60])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (r1_tmap_1(X1,X2,k2_tmap_1(esk4_0,X2,X3,X1),esk7_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(esk4_0,X2,X3,esk7_0)|~r1_tarski(esk6_0,u1_struct_0(X1))|~v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_42]), c_0_43]), c_0_28]), c_0_30])]), c_0_32])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)|~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_62, c_0_60])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_29])]), c_0_31]), c_0_64])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk4_0,X1,X2,esk7_0)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_56]), c_0_57]), c_0_38])]), c_0_58])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_24]), c_0_67]), c_0_25]), c_0_26]), c_0_27]), c_0_29])]), c_0_69]), c_0_31]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 71
% 0.12/0.37  # Proof object clause steps            : 54
% 0.12/0.37  # Proof object formula steps           : 17
% 0.12/0.37  # Proof object conjectures             : 46
% 0.12/0.37  # Proof object clause conjectures      : 43
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 30
% 0.12/0.37  # Proof object initial formulas used   : 8
% 0.12/0.37  # Proof object generating inferences   : 15
% 0.12/0.37  # Proof object simplifying inferences  : 76
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 8
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 31
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 31
% 0.12/0.37  # Processed clauses                    : 87
% 0.12/0.37  # ...of these trivial                  : 1
% 0.12/0.37  # ...subsumed                          : 0
% 0.12/0.37  # ...remaining for further processing  : 86
% 0.12/0.37  # Other redundant clauses eliminated   : 2
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 4
% 0.12/0.37  # Generated clauses                    : 25
% 0.12/0.37  # ...of the previous two non-trivial   : 25
% 0.12/0.37  # Contextual simplify-reflections      : 2
% 0.12/0.37  # Paramodulations                      : 23
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 2
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 49
% 0.12/0.37  #    Positive orientable unit clauses  : 25
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 5
% 0.12/0.37  #    Non-unit-clauses                  : 19
% 0.12/0.37  # Current number of unprocessed clauses: 0
% 0.12/0.37  # ...number of literals in the above   : 0
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 35
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 509
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 50
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.37  # Unit Clause-clause subsumption calls : 1
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 3
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4793
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.036 s
% 0.12/0.37  # System time              : 0.003 s
% 0.12/0.37  # Total time               : 0.039 s
% 0.12/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
