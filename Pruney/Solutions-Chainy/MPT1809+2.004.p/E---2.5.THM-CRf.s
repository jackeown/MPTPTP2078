%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:31 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   66 (1510 expanded)
%              Number of clauses        :   55 ( 450 expanded)
%              Number of leaves         :    5 ( 363 expanded)
%              Depth                    :   11
%              Number of atoms          :  485 (25439 expanded)
%              Number of equality atoms :   38 (3167 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal clause size      :   61 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( X1 = k1_tsep_1(X1,X4,X5)
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X5))
                                   => ( ( X6 = X7
                                        & X6 = X8 )
                                     => ( r1_tmap_1(X1,X2,X3,X6)
                                      <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                          & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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

fof(t123_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ! [X8] :
                                  ( m1_subset_1(X8,u1_struct_0(k1_tsep_1(X1,X3,X4)))
                                 => ( ( X8 = X6
                                      & X8 = X7 )
                                   => ( r1_tmap_1(k1_tsep_1(X1,X3,X4),X2,X5,X8)
                                    <=> ( r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X6)
                                        & r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X7) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_tmap_1)).

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

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( X1 = k1_tsep_1(X1,X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X5))
                                     => ( ( X6 = X7
                                          & X6 = X8 )
                                       => ( r1_tmap_1(X1,X2,X3,X6)
                                        <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                            & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t125_tmap_1])).

fof(c_0_6,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_struct_0(k1_tsep_1(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18) )
      & ( v1_pre_topc(k1_tsep_1(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18) )
      & ( m1_pre_topc(k1_tsep_1(X18,X19,X20),X18)
        | v2_struct_0(X18)
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & esk6_0 = esk7_0
    & esk6_0 = esk8_0
    & ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
      | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
      | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) )
    & ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
      | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) )
    & ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
      | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).

fof(c_0_8,plain,(
    ! [X9,X10,X11,X12] :
      ( v2_struct_0(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ v1_funct_1(X11)
      | ~ v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))
      | ~ m1_pre_topc(X12,X9)
      | k2_tmap_1(X9,X10,X11,X12) = k2_partfun1(u1_struct_0(X9),u1_struct_0(X10),X11,u1_struct_0(X12)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_9,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( r1_tmap_1(X23,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X23,X25),X26)
        | ~ r1_tmap_1(k1_tsep_1(X21,X23,X24),X22,X25,X28)
        | X28 != X26
        | X28 != X27
        | ~ m1_subset_1(X28,u1_struct_0(k1_tsep_1(X21,X23,X24)))
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tmap_1(X24,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X24,X25),X27)
        | ~ r1_tmap_1(k1_tsep_1(X21,X23,X24),X22,X25,X28)
        | X28 != X26
        | X28 != X27
        | ~ m1_subset_1(X28,u1_struct_0(k1_tsep_1(X21,X23,X24)))
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( ~ r1_tmap_1(X23,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X23,X25),X26)
        | ~ r1_tmap_1(X24,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X24,X25),X27)
        | r1_tmap_1(k1_tsep_1(X21,X23,X24),X22,X25,X28)
        | X28 != X26
        | X28 != X27
        | ~ m1_subset_1(X28,u1_struct_0(k1_tsep_1(X21,X23,X24)))
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X21)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t123_tmap_1])])])])])).

fof(c_0_10,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X13)
      | ~ m1_pre_topc(X16,X13)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))
      | ~ m1_pre_topc(X16,X15)
      | k3_tmap_1(X13,X14,X15,X16,X17) = k2_partfun1(u1_struct_0(X15),u1_struct_0(X14),X17,u1_struct_0(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

cnf(c_0_11,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X8)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)
    | ~ r1_tmap_1(X4,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,X5),X7)
    | X8 != X6
    | X8 != X7
    | ~ m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X4)))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_13]),c_0_21]),c_0_22])]),c_0_23]),c_0_15])).

cnf(c_0_31,plain,
    ( r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,X5,X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X4,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X6)
    | ~ r1_tmap_1(X2,X4,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X6)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_23])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_36,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(k1_tsep_1(X3,X4,X1),X2,X5,X7)
    | X7 != X8
    | X7 != X6
    | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X4,X1)))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X8,u1_struct_0(X4))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X4,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_37,negated_conjecture,
    ( r1_tmap_1(esk1_0,X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),X3)
    | ~ r1_tmap_1(esk4_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_28]),c_0_12]),c_0_27]),c_0_13]),c_0_22])]),c_0_29]),c_0_15]),c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_12]),c_0_12]),c_0_33]),c_0_13]),c_0_22])]),c_0_15]),c_0_34])).

cnf(c_0_39,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_27]),c_0_33]),c_0_13]),c_0_22])]),c_0_15]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_46,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X4,X1),X2,X5,X6)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X3,X4,X1)))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).

cnf(c_0_47,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X7)
    | X7 != X6
    | X7 != X8
    | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X4)))
    | ~ m1_subset_1(X8,u1_struct_0(X4))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_49,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_23]),c_0_38]),c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_42,c_0_41])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_44])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk5_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk1_0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_28]),c_0_27]),c_0_12]),c_0_13]),c_0_22])]),c_0_14]),c_0_15]),c_0_29])).

cnf(c_0_56,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X6)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X3,X1,X4)))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_44]),c_0_41])).

cnf(c_0_58,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52]),c_0_53])]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_23]),c_0_38])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk1_0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_28]),c_0_12]),c_0_27]),c_0_13]),c_0_22])]),c_0_29]),c_0_15]),c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_58]),c_0_51]),c_0_53]),c_0_52])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21])]),c_0_23]),c_0_39])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_51]),c_0_52]),c_0_53])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.44/2.60  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 2.44/2.60  # and selection function SelectCQIPrecWNTNp.
% 2.44/2.60  #
% 2.44/2.60  # Preprocessing time       : 0.028 s
% 2.44/2.60  # Presaturation interreduction done
% 2.44/2.60  
% 2.44/2.60  # Proof found!
% 2.44/2.60  # SZS status Theorem
% 2.44/2.60  # SZS output start CNFRefutation
% 2.44/2.60  fof(t125_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 2.44/2.60  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 2.44/2.60  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 2.44/2.60  fof(t123_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(k1_tsep_1(X1,X3,X4)))=>((X8=X6&X8=X7)=>(r1_tmap_1(k1_tsep_1(X1,X3,X4),X2,X5,X8)<=>(r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X6)&r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X7)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_tmap_1)).
% 2.44/2.60  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 2.44/2.60  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))))), inference(assume_negation,[status(cth)],[t125_tmap_1])).
% 2.44/2.60  fof(c_0_6, plain, ![X18, X19, X20]:(((~v2_struct_0(k1_tsep_1(X18,X19,X20))|(v2_struct_0(X18)|~l1_pre_topc(X18)|v2_struct_0(X19)|~m1_pre_topc(X19,X18)|v2_struct_0(X20)|~m1_pre_topc(X20,X18)))&(v1_pre_topc(k1_tsep_1(X18,X19,X20))|(v2_struct_0(X18)|~l1_pre_topc(X18)|v2_struct_0(X19)|~m1_pre_topc(X19,X18)|v2_struct_0(X20)|~m1_pre_topc(X20,X18))))&(m1_pre_topc(k1_tsep_1(X18,X19,X20),X18)|(v2_struct_0(X18)|~l1_pre_topc(X18)|v2_struct_0(X19)|~m1_pre_topc(X19,X18)|v2_struct_0(X20)|~m1_pre_topc(X20,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 2.44/2.60  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk1_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((esk6_0=esk7_0&esk6_0=esk8_0)&((~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|(~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)))&((r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0))&(r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 2.44/2.60  fof(c_0_8, plain, ![X9, X10, X11, X12]:(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))|(~m1_pre_topc(X12,X9)|k2_tmap_1(X9,X10,X11,X12)=k2_partfun1(u1_struct_0(X9),u1_struct_0(X10),X11,u1_struct_0(X12)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 2.44/2.60  fof(c_0_9, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:(((r1_tmap_1(X23,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X23,X25),X26)|~r1_tmap_1(k1_tsep_1(X21,X23,X24),X22,X25,X28)|(X28!=X26|X28!=X27)|~m1_subset_1(X28,u1_struct_0(k1_tsep_1(X21,X23,X24)))|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X23))|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22)))))|(v2_struct_0(X24)|~m1_pre_topc(X24,X21))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(r1_tmap_1(X24,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X24,X25),X27)|~r1_tmap_1(k1_tsep_1(X21,X23,X24),X22,X25,X28)|(X28!=X26|X28!=X27)|~m1_subset_1(X28,u1_struct_0(k1_tsep_1(X21,X23,X24)))|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X23))|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22)))))|(v2_struct_0(X24)|~m1_pre_topc(X24,X21))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(~r1_tmap_1(X23,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X23,X25),X26)|~r1_tmap_1(X24,X22,k3_tmap_1(X21,X22,k1_tsep_1(X21,X23,X24),X24,X25),X27)|r1_tmap_1(k1_tsep_1(X21,X23,X24),X22,X25,X28)|(X28!=X26|X28!=X27)|~m1_subset_1(X28,u1_struct_0(k1_tsep_1(X21,X23,X24)))|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X23))|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X23,X24)),u1_struct_0(X22)))))|(v2_struct_0(X24)|~m1_pre_topc(X24,X21))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t123_tmap_1])])])])])).
% 2.44/2.60  fof(c_0_10, plain, ![X13, X14, X15, X16, X17]:(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|(~m1_pre_topc(X15,X13)|(~m1_pre_topc(X16,X13)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))|(~m1_pre_topc(X16,X15)|k3_tmap_1(X13,X14,X15,X16,X17)=k2_partfun1(u1_struct_0(X15),u1_struct_0(X14),X17,u1_struct_0(X16)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 2.44/2.60  cnf(c_0_11, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 2.44/2.60  cnf(c_0_12, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_16, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 2.44/2.60  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_24, plain, (r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X8)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|~r1_tmap_1(X4,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,X5),X7)|X8!=X6|X8!=X7|~m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X4)))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.44/2.60  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 2.44/2.60  cnf(c_0_26, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 2.44/2.60  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_28, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_30, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_13]), c_0_21]), c_0_22])]), c_0_23]), c_0_15])).
% 2.44/2.60  cnf(c_0_31, plain, (r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,X5,X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X3,X4,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X6)|~r1_tmap_1(X2,X4,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X6)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X6,u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))|~v1_funct_1(X5)|~l1_pre_topc(X1)|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~v2_pre_topc(X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 2.44/2.60  cnf(c_0_32, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_23])).
% 2.44/2.60  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 2.44/2.60  cnf(c_0_34, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_30, c_0_12])).
% 2.44/2.60  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 2.44/2.60  cnf(c_0_36, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X4,X1),X2,X5,X7)|X7!=X8|X7!=X6|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X4,X1)))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(X4))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.44/2.60  cnf(c_0_37, negated_conjecture, (r1_tmap_1(esk1_0,X1,X2,X3)|v2_struct_0(X1)|~r1_tmap_1(esk5_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),X3)|~r1_tmap_1(esk4_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_28]), c_0_12]), c_0_27]), c_0_13]), c_0_22])]), c_0_29]), c_0_15]), c_0_14])).
% 2.44/2.60  cnf(c_0_38, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_12]), c_0_12]), c_0_33]), c_0_13]), c_0_22])]), c_0_15]), c_0_34])).
% 2.44/2.60  cnf(c_0_39, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_27]), c_0_33]), c_0_13]), c_0_22])]), c_0_15]), c_0_35])).
% 2.44/2.60  cnf(c_0_40, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_41, negated_conjecture, (esk6_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_44, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_45, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_46, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X4,X1),X2,X5,X6)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X3,X4,X1)))|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))|~v1_funct_1(X5)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_36])])).
% 2.44/2.60  cnf(c_0_47, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X7)|X7!=X6|X7!=X8|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X4)))|~m1_subset_1(X8,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 2.44/2.60  cnf(c_0_48, negated_conjecture, (~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_49, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_23]), c_0_38]), c_0_39])).
% 2.44/2.60  cnf(c_0_50, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_40, c_0_41])).
% 2.44/2.60  cnf(c_0_51, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 2.44/2.60  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_42, c_0_41])).
% 2.44/2.60  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 2.44/2.60  cnf(c_0_54, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_45, c_0_44])).
% 2.44/2.60  cnf(c_0_55, negated_conjecture, (r1_tmap_1(esk5_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),X3)|v2_struct_0(X1)|~r1_tmap_1(esk1_0,X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_28]), c_0_27]), c_0_12]), c_0_13]), c_0_22])]), c_0_14]), c_0_15]), c_0_29])).
% 2.44/2.60  cnf(c_0_56, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X6)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X3,X1,X4)))|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~v1_funct_1(X5)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 2.44/2.60  cnf(c_0_57, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_44]), c_0_41])).
% 2.44/2.60  cnf(c_0_58, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52]), c_0_53])]), c_0_54])).
% 2.44/2.60  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_23]), c_0_38])).
% 2.44/2.60  cnf(c_0_60, negated_conjecture, (r1_tmap_1(esk4_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),X3)|v2_struct_0(X1)|~r1_tmap_1(esk1_0,X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_28]), c_0_12]), c_0_27]), c_0_13]), c_0_22])]), c_0_29]), c_0_15]), c_0_14])).
% 2.44/2.60  cnf(c_0_61, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_58])])).
% 2.44/2.60  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_58]), c_0_51]), c_0_53]), c_0_52])])).
% 2.44/2.60  cnf(c_0_63, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21])]), c_0_23]), c_0_39])).
% 2.44/2.60  cnf(c_0_64, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 2.44/2.60  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58]), c_0_51]), c_0_52]), c_0_53])]), c_0_64]), ['proof']).
% 2.44/2.60  # SZS output end CNFRefutation
% 2.44/2.60  # Proof object total steps             : 66
% 2.44/2.60  # Proof object clause steps            : 55
% 2.44/2.60  # Proof object formula steps           : 11
% 2.44/2.60  # Proof object conjectures             : 49
% 2.44/2.60  # Proof object clause conjectures      : 46
% 2.44/2.60  # Proof object formula conjectures     : 3
% 2.44/2.60  # Proof object initial clauses used    : 28
% 2.44/2.60  # Proof object initial formulas used   : 5
% 2.44/2.60  # Proof object generating inferences   : 17
% 2.44/2.60  # Proof object simplifying inferences  : 111
% 2.44/2.60  # Training examples: 0 positive, 0 negative
% 2.44/2.60  # Parsed axioms                        : 5
% 2.44/2.60  # Removed by relevancy pruning/SinE    : 0
% 2.44/2.60  # Initial clauses                      : 30
% 2.44/2.60  # Removed in clause preprocessing      : 0
% 2.44/2.60  # Initial clauses in saturation        : 30
% 2.44/2.60  # Processed clauses                    : 5558
% 2.44/2.60  # ...of these trivial                  : 0
% 2.44/2.60  # ...subsumed                          : 1
% 2.44/2.60  # ...remaining for further processing  : 5556
% 2.44/2.60  # Other redundant clauses eliminated   : 6
% 2.44/2.60  # Clauses deleted for lack of memory   : 0
% 2.44/2.60  # Backward-subsumed                    : 0
% 2.44/2.60  # Backward-rewritten                   : 33
% 2.44/2.60  # Generated clauses                    : 359283
% 2.44/2.60  # ...of the previous two non-trivial   : 359313
% 2.44/2.60  # Contextual simplify-reflections      : 1
% 2.44/2.60  # Paramodulations                      : 359280
% 2.44/2.60  # Factorizations                       : 0
% 2.44/2.60  # Equation resolutions                 : 6
% 2.44/2.60  # Propositional unsat checks           : 0
% 2.44/2.60  #    Propositional check models        : 0
% 2.44/2.60  #    Propositional check unsatisfiable : 0
% 2.44/2.60  #    Propositional clauses             : 0
% 2.44/2.60  #    Propositional clauses after purity: 0
% 2.44/2.60  #    Propositional unsat core size     : 0
% 2.44/2.60  #    Propositional preprocessing time  : 0.000
% 2.44/2.60  #    Propositional encoding time       : 0.000
% 2.44/2.60  #    Propositional solver time         : 0.000
% 2.44/2.60  #    Success case prop preproc time    : 0.000
% 2.44/2.60  #    Success case prop encoding time   : 0.000
% 2.44/2.60  #    Success case prop solver time     : 0.000
% 2.44/2.60  # Current number of processed clauses  : 5490
% 2.44/2.60  #    Positive orientable unit clauses  : 1273
% 2.44/2.60  #    Positive unorientable unit clauses: 0
% 2.44/2.60  #    Negative unit clauses             : 3595
% 2.44/2.60  #    Non-unit-clauses                  : 622
% 2.44/2.60  # Current number of unprocessed clauses: 353815
% 2.44/2.60  # ...number of literals in the above   : 368823
% 2.44/2.60  # Current number of archived formulas  : 0
% 2.44/2.60  # Current number of archived clauses   : 63
% 2.44/2.60  # Clause-clause subsumption calls (NU) : 69239
% 2.44/2.60  # Rec. Clause-clause subsumption calls : 68150
% 2.44/2.60  # Non-unit clause-clause subsumptions  : 1
% 2.44/2.60  # Unit Clause-clause subsumption calls : 335230
% 2.44/2.60  # Rewrite failures with RHS unbound    : 0
% 2.44/2.60  # BW rewrite match attempts            : 223972
% 2.44/2.60  # BW rewrite match successes           : 31
% 2.44/2.60  # Condensation attempts                : 0
% 2.44/2.60  # Condensation successes               : 0
% 2.44/2.60  # Termbank termtop insertions          : 14535334
% 2.44/2.62  
% 2.44/2.62  # -------------------------------------------------
% 2.44/2.62  # User time                : 2.119 s
% 2.44/2.62  # System time              : 0.160 s
% 2.44/2.62  # Total time               : 2.279 s
% 2.44/2.62  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
