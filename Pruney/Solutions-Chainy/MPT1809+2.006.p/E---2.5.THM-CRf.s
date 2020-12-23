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
% DateTime   : Thu Dec  3 11:18:31 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   65 (1309 expanded)
%              Number of clauses        :   54 ( 393 expanded)
%              Number of leaves         :    5 ( 315 expanded)
%              Depth                    :   11
%              Number of atoms          :  452 (21765 expanded)
%              Number of equality atoms :   40 (2735 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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

cnf(c_0_9,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_19,plain,(
    ! [X18,X19,X20,X21,X22,X23,X24,X25] :
      ( ( r1_tmap_1(X20,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X20,X22),X23)
        | ~ r1_tmap_1(k1_tsep_1(X18,X20,X21),X19,X22,X25)
        | X25 != X23
        | X25 != X24
        | ~ m1_subset_1(X25,u1_struct_0(k1_tsep_1(X18,X20,X21)))
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))))
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( r1_tmap_1(X21,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X21,X22),X24)
        | ~ r1_tmap_1(k1_tsep_1(X18,X20,X21),X19,X22,X25)
        | X25 != X23
        | X25 != X24
        | ~ m1_subset_1(X25,u1_struct_0(k1_tsep_1(X18,X20,X21)))
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))))
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( ~ r1_tmap_1(X20,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X20,X22),X23)
        | ~ r1_tmap_1(X21,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X21,X22),X24)
        | r1_tmap_1(k1_tsep_1(X18,X20,X21),X19,X22,X25)
        | X25 != X23
        | X25 != X24
        | ~ m1_subset_1(X25,u1_struct_0(k1_tsep_1(X18,X20,X21)))
        | ~ m1_subset_1(X24,u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X20))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))))
        | v2_struct_0(X21)
        | ~ m1_pre_topc(X21,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19)
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t123_tmap_1])])])])])).

cnf(c_0_20,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_15])]),c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_27,plain,(
    ! [X26] :
      ( ~ l1_pre_topc(X26)
      | m1_pre_topc(X26,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_28,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_23])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
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

cnf(c_0_31,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)
    | ~ m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_22]),c_0_26]),c_0_22]),c_0_14]),c_0_16])]),c_0_18])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)
    | ~ m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_23]),c_0_28]),c_0_23]),c_0_14]),c_0_16])]),c_0_18])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,plain,
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
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).

cnf(c_0_39,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_22]),c_0_23]),c_0_14]),c_0_16])]),c_0_32]),c_0_18]),c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_14])])).

cnf(c_0_41,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0) = k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_14])])).

cnf(c_0_42,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_47,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_48,plain,
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
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_49,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_31]),c_0_22]),c_0_23]),c_0_14]),c_0_16])]),c_0_32]),c_0_18]),c_0_33])).

cnf(c_0_50,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_10]),c_0_40]),c_0_41]),c_0_11]),c_0_12]),c_0_13]),c_0_15])]),c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_46])).

cnf(c_0_56,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_23]),c_0_22]),c_0_14]),c_0_16])]),c_0_33]),c_0_18]),c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_58,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_10]),c_0_41]),c_0_11]),c_0_12]),c_0_13]),c_0_15])]),c_0_17])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53]),c_0_54])]),c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_10]),c_0_40]),c_0_11]),c_0_12]),c_0_13]),c_0_15])]),c_0_17])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_46]),c_0_43])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_52]),c_0_53]),c_0_54])])).

cnf(c_0_63,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_59]),c_0_52]),c_0_54]),c_0_53])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_59])]),c_0_62]),c_0_63])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n008.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 11:06:00 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.32  # No SInE strategy applied
% 0.11/0.32  # Trying AutoSched0 for 299 seconds
% 0.18/0.34  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.34  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.34  #
% 0.18/0.34  # Preprocessing time       : 0.014 s
% 0.18/0.34  # Presaturation interreduction done
% 0.18/0.34  
% 0.18/0.34  # Proof found!
% 0.18/0.34  # SZS status Theorem
% 0.18/0.34  # SZS output start CNFRefutation
% 0.18/0.34  fof(t125_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_tmap_1)).
% 0.18/0.34  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.34  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.18/0.34  fof(t123_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X3,X4)),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(k1_tsep_1(X1,X3,X4)))=>((X8=X6&X8=X7)=>(r1_tmap_1(k1_tsep_1(X1,X3,X4),X2,X5,X8)<=>(r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X3,X5),X6)&r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,k1_tsep_1(X1,X3,X4),X4,X5),X7)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_tmap_1)).
% 0.18/0.34  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.18/0.34  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))))), inference(assume_negation,[status(cth)],[t125_tmap_1])).
% 0.18/0.34  fof(c_0_6, plain, ![X9, X10, X11, X12]:(v2_struct_0(X9)|~v2_pre_topc(X9)|~l1_pre_topc(X9)|(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|(~v1_funct_1(X11)|~v1_funct_2(X11,u1_struct_0(X9),u1_struct_0(X10))|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(X10))))|(~m1_pre_topc(X12,X9)|k2_tmap_1(X9,X10,X11,X12)=k2_partfun1(u1_struct_0(X9),u1_struct_0(X10),X11,u1_struct_0(X12)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.34  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk1_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((esk6_0=esk7_0&esk6_0=esk8_0)&((~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|(~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)))&((r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0))&(r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])])).
% 0.18/0.34  fof(c_0_8, plain, ![X13, X14, X15, X16, X17]:(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|(~m1_pre_topc(X15,X13)|(~m1_pre_topc(X16,X13)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X14))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X14))))|(~m1_pre_topc(X16,X15)|k3_tmap_1(X13,X14,X15,X16,X17)=k2_partfun1(u1_struct_0(X15),u1_struct_0(X14),X17,u1_struct_0(X16)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.18/0.34  cnf(c_0_9, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.34  cnf(c_0_10, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_11, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_12, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_13, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  fof(c_0_19, plain, ![X18, X19, X20, X21, X22, X23, X24, X25]:(((r1_tmap_1(X20,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X20,X22),X23)|~r1_tmap_1(k1_tsep_1(X18,X20,X21),X19,X22,X25)|(X25!=X23|X25!=X24)|~m1_subset_1(X25,u1_struct_0(k1_tsep_1(X18,X20,X21)))|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X20))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19)))))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(r1_tmap_1(X21,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X21,X22),X24)|~r1_tmap_1(k1_tsep_1(X18,X20,X21),X19,X22,X25)|(X25!=X23|X25!=X24)|~m1_subset_1(X25,u1_struct_0(k1_tsep_1(X18,X20,X21)))|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X20))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19)))))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18))))&(~r1_tmap_1(X20,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X20,X22),X23)|~r1_tmap_1(X21,X19,k3_tmap_1(X18,X19,k1_tsep_1(X18,X20,X21),X21,X22),X24)|r1_tmap_1(k1_tsep_1(X18,X20,X21),X19,X22,X25)|(X25!=X23|X25!=X24)|~m1_subset_1(X25,u1_struct_0(k1_tsep_1(X18,X20,X21)))|~m1_subset_1(X24,u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X20))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X18,X20,X21)),u1_struct_0(X19)))))|(v2_struct_0(X21)|~m1_pre_topc(X21,X18))|(v2_struct_0(X20)|~m1_pre_topc(X20,X18))|(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t123_tmap_1])])])])])).
% 0.18/0.34  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.18/0.34  cnf(c_0_21, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_18])).
% 0.18/0.34  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_24, plain, (r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X8)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|~r1_tmap_1(X4,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X4,X5),X7)|X8!=X6|X8!=X7|~m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X4)))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.34  cnf(c_0_25, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk3_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_15])]), c_0_17])).
% 0.18/0.34  cnf(c_0_26, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk5_0))=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.18/0.34  fof(c_0_27, plain, ![X26]:(~l1_pre_topc(X26)|m1_pre_topc(X26,X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.18/0.34  cnf(c_0_28, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk4_0))=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(spm,[status(thm)],[c_0_21, c_0_23])).
% 0.18/0.34  cnf(c_0_29, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X7)|X7!=X6|X7!=X8|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X4)))|~m1_subset_1(X8,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.34  cnf(c_0_30, plain, (r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,X5,X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X3,X4,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X3,X5),X6)|~r1_tmap_1(X2,X4,k3_tmap_1(X1,X4,k1_tsep_1(X1,X2,X3),X2,X5),X6)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X6,u1_struct_0(X2))|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X1,X2,X3)),u1_struct_0(X4))|~v1_funct_1(X5)|~l1_pre_topc(X1)|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~v2_pre_topc(X4)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.18/0.34  cnf(c_0_31, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_34, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)|~m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_22]), c_0_26]), c_0_22]), c_0_14]), c_0_16])]), c_0_18])).
% 0.18/0.34  cnf(c_0_35, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.18/0.34  cnf(c_0_36, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)|~m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_23]), c_0_28]), c_0_23]), c_0_14]), c_0_16])]), c_0_18])).
% 0.18/0.34  cnf(c_0_37, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X4,X1),X2,X5,X7)|X7!=X8|X7!=X6|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X4,X1)))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(X4))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))|~m1_pre_topc(X1,X3)|~m1_pre_topc(X4,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.34  cnf(c_0_38, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X1,X4),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X1,X4),X2,X5,X6)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X3,X1,X4)))|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X1,X4)),u1_struct_0(X2))|~v1_funct_1(X5)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_29])])).
% 0.18/0.34  cnf(c_0_39, negated_conjecture, (r1_tmap_1(esk1_0,X1,X2,X3)|v2_struct_0(X1)|~r1_tmap_1(esk5_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),X3)|~r1_tmap_1(esk4_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_22]), c_0_23]), c_0_14]), c_0_16])]), c_0_32]), c_0_18]), c_0_33])).
% 0.18/0.34  cnf(c_0_40, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk5_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_14])])).
% 0.18/0.34  cnf(c_0_41, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk3_0)=k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_14])])).
% 0.18/0.34  cnf(c_0_42, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_43, negated_conjecture, (esk6_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_46, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_47, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_48, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,k1_tsep_1(X3,X4,X1),X1,X5),X6)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X4,X1),X2,X5,X6)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X3,X4,X1)))|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X6,u1_struct_0(X1))|~v1_funct_2(X5,u1_struct_0(k1_tsep_1(X3,X4,X1)),u1_struct_0(X2))|~v1_funct_1(X5)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).
% 0.18/0.34  cnf(c_0_49, negated_conjecture, (r1_tmap_1(esk4_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk4_0,X2),X3)|v2_struct_0(X1)|~r1_tmap_1(esk1_0,X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_31]), c_0_22]), c_0_23]), c_0_14]), c_0_16])]), c_0_32]), c_0_18]), c_0_33])).
% 0.18/0.34  cnf(c_0_50, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_10]), c_0_40]), c_0_41]), c_0_11]), c_0_12]), c_0_13]), c_0_15])]), c_0_17])).
% 0.18/0.34  cnf(c_0_51, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_42, c_0_43])).
% 0.18/0.34  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_44, c_0_43])).
% 0.18/0.34  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_45, c_0_46])).
% 0.18/0.34  cnf(c_0_55, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_47, c_0_46])).
% 0.18/0.34  cnf(c_0_56, negated_conjecture, (r1_tmap_1(esk5_0,X1,k3_tmap_1(esk1_0,X1,esk1_0,esk5_0,X2),X3)|v2_struct_0(X1)|~r1_tmap_1(esk1_0,X1,X2,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))|~m1_subset_1(X3,u1_struct_0(esk1_0))|~m1_subset_1(X3,u1_struct_0(esk4_0))|~m1_subset_1(X3,u1_struct_0(esk5_0))|~v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_31]), c_0_23]), c_0_22]), c_0_14]), c_0_16])]), c_0_33]), c_0_18]), c_0_32])).
% 0.18/0.34  cnf(c_0_57, negated_conjecture, (~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.34  cnf(c_0_58, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_10]), c_0_41]), c_0_11]), c_0_12]), c_0_13]), c_0_15])]), c_0_17])).
% 0.18/0.34  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53]), c_0_54])]), c_0_55])).
% 0.18/0.34  cnf(c_0_60, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_10]), c_0_40]), c_0_11]), c_0_12]), c_0_13]), c_0_15])]), c_0_17])).
% 0.18/0.34  cnf(c_0_61, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_46]), c_0_43])).
% 0.18/0.34  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_52]), c_0_53]), c_0_54])])).
% 0.18/0.34  cnf(c_0_63, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_59]), c_0_52]), c_0_54]), c_0_53])])).
% 0.18/0.34  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_59])]), c_0_62]), c_0_63])]), ['proof']).
% 0.18/0.34  # SZS output end CNFRefutation
% 0.18/0.34  # Proof object total steps             : 65
% 0.18/0.34  # Proof object clause steps            : 54
% 0.18/0.34  # Proof object formula steps           : 11
% 0.18/0.34  # Proof object conjectures             : 48
% 0.18/0.34  # Proof object clause conjectures      : 45
% 0.18/0.34  # Proof object formula conjectures     : 3
% 0.18/0.34  # Proof object initial clauses used    : 28
% 0.18/0.34  # Proof object initial formulas used   : 5
% 0.18/0.34  # Proof object generating inferences   : 17
% 0.18/0.34  # Proof object simplifying inferences  : 107
% 0.18/0.34  # Training examples: 0 positive, 0 negative
% 0.18/0.34  # Parsed axioms                        : 5
% 0.18/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.34  # Initial clauses                      : 28
% 0.18/0.34  # Removed in clause preprocessing      : 0
% 0.18/0.34  # Initial clauses in saturation        : 28
% 0.18/0.34  # Processed clauses                    : 83
% 0.18/0.34  # ...of these trivial                  : 0
% 0.18/0.34  # ...subsumed                          : 0
% 0.18/0.34  # ...remaining for further processing  : 82
% 0.18/0.34  # Other redundant clauses eliminated   : 6
% 0.18/0.34  # Clauses deleted for lack of memory   : 0
% 0.18/0.34  # Backward-subsumed                    : 0
% 0.18/0.34  # Backward-rewritten                   : 6
% 0.18/0.34  # Generated clauses                    : 27
% 0.18/0.34  # ...of the previous two non-trivial   : 27
% 0.18/0.34  # Contextual simplify-reflections      : 1
% 0.18/0.34  # Paramodulations                      : 24
% 0.18/0.34  # Factorizations                       : 0
% 0.18/0.34  # Equation resolutions                 : 6
% 0.18/0.34  # Propositional unsat checks           : 0
% 0.18/0.34  #    Propositional check models        : 0
% 0.18/0.34  #    Propositional check unsatisfiable : 0
% 0.18/0.34  #    Propositional clauses             : 0
% 0.18/0.34  #    Propositional clauses after purity: 0
% 0.18/0.34  #    Propositional unsat core size     : 0
% 0.18/0.34  #    Propositional preprocessing time  : 0.000
% 0.18/0.34  #    Propositional encoding time       : 0.000
% 0.18/0.34  #    Propositional solver time         : 0.000
% 0.18/0.34  #    Success case prop preproc time    : 0.000
% 0.18/0.34  #    Success case prop encoding time   : 0.000
% 0.18/0.34  #    Success case prop solver time     : 0.000
% 0.18/0.34  # Current number of processed clauses  : 45
% 0.18/0.34  #    Positive orientable unit clauses  : 24
% 0.18/0.34  #    Positive unorientable unit clauses: 0
% 0.18/0.34  #    Negative unit clauses             : 4
% 0.18/0.34  #    Non-unit-clauses                  : 17
% 0.18/0.34  # Current number of unprocessed clauses: 0
% 0.18/0.34  # ...number of literals in the above   : 0
% 0.18/0.34  # Current number of archived formulas  : 0
% 0.18/0.34  # Current number of archived clauses   : 34
% 0.18/0.34  # Clause-clause subsumption calls (NU) : 389
% 0.18/0.34  # Rec. Clause-clause subsumption calls : 16
% 0.18/0.34  # Non-unit clause-clause subsumptions  : 1
% 0.18/0.34  # Unit Clause-clause subsumption calls : 15
% 0.18/0.34  # Rewrite failures with RHS unbound    : 0
% 0.18/0.34  # BW rewrite match attempts            : 17
% 0.18/0.34  # BW rewrite match successes           : 4
% 0.18/0.34  # Condensation attempts                : 0
% 0.18/0.34  # Condensation successes               : 0
% 0.18/0.34  # Termbank termtop insertions          : 5101
% 0.18/0.34  
% 0.18/0.34  # -------------------------------------------------
% 0.18/0.34  # User time                : 0.018 s
% 0.18/0.34  # System time              : 0.002 s
% 0.18/0.34  # Total time               : 0.020 s
% 0.18/0.34  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
