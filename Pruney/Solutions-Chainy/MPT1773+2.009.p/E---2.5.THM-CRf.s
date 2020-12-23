%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:47 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 691 expanded)
%              Number of clauses        :   53 ( 220 expanded)
%              Number of leaves         :    7 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  462 (11071 expanded)
%              Number of equality atoms :   21 ( 477 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal clause size      :   40 (   5 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

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

fof(t66_tmap_1,axiom,(
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
                             => ( ( v3_pre_topc(X5,X2)
                                  & r2_hidden(X6,X5)
                                  & r1_tarski(X5,u1_struct_0(X4))
                                  & X6 = X7 )
                               => ( r1_tmap_1(X2,X1,X3,X6)
                                <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

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

fof(c_0_8,plain,(
    ! [X11,X12] :
      ( ~ l1_pre_topc(X11)
      | ~ m1_pre_topc(X12,X11)
      | l1_pre_topc(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_9,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_10,plain,(
    ! [X9,X10] :
      ( ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | v2_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X17)
      | ~ m1_pre_topc(X20,X17)
      | ~ v1_funct_1(X21)
      | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X18))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))
      | ~ m1_pre_topc(X20,X19)
      | k3_tmap_1(X17,X18,X19,X20,X21) = k2_partfun1(u1_struct_0(X19),u1_struct_0(X18),X21,u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_12,plain,(
    ! [X29,X30,X31] :
      ( ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_pre_topc(X30,X29)
      | ~ m1_pre_topc(X31,X30)
      | m1_pre_topc(X31,X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_13,plain,(
    ! [X13,X14,X15,X16] :
      ( v2_struct_0(X13)
      | ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ v1_funct_1(X15)
      | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
      | ~ m1_pre_topc(X16,X13)
      | k2_tmap_1(X13,X14,X15,X16) = k2_partfun1(u1_struct_0(X13),u1_struct_0(X14),X15,u1_struct_0(X16)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_14,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_19,plain,(
    ! [X22,X23,X24,X25,X26,X27,X28] :
      ( ( ~ r1_tmap_1(X23,X22,X24,X27)
        | r1_tmap_1(X25,X22,k2_tmap_1(X23,X22,X24,X25),X28)
        | ~ v3_pre_topc(X26,X23)
        | ~ r2_hidden(X27,X26)
        | ~ r1_tarski(X26,u1_struct_0(X25))
        | X27 != X28
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( ~ r1_tmap_1(X25,X22,k2_tmap_1(X23,X22,X24,X25),X28)
        | r1_tmap_1(X23,X22,X24,X27)
        | ~ v3_pre_topc(X26,X23)
        | ~ r2_hidden(X27,X26)
        | ~ r1_tarski(X26,u1_struct_0(X25))
        | X27 != X28
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X23))
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X23)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22))))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23)
        | v2_struct_0(X22)
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_tmap_1])])])])])).

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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16])])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_15]),c_0_16]),c_0_18])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_32,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ v3_pre_topc(X7,X3)
    | ~ r2_hidden(X6,X7)
    | ~ r1_tarski(X7,u1_struct_0(X1))
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

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
    inference(csr,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk2_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_36,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ r1_tarski(X6,u1_struct_0(X5))
    | ~ r2_hidden(X4,X6)
    | ~ v3_pre_topc(X6,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_40,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_28])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ v3_pre_topc(X7,X1)
    | ~ r2_hidden(X4,X7)
    | ~ r1_tarski(X7,u1_struct_0(X5))
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
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk3_0,X2,k2_tmap_1(X1,X2,X3,esk3_0),X4)
    | ~ r2_hidden(X4,esk6_0)
    | ~ v3_pre_topc(esk6_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
    | r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_48,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk5_0) = k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ r1_tarski(X6,u1_struct_0(X1))
    | ~ r2_hidden(X5,X6)
    | ~ v3_pre_topc(X6,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)
    | ~ r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_52,negated_conjecture,
    ( r1_tmap_1(X1,X2,X3,esk7_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk3_0,X2,k2_tmap_1(X1,X2,X3,esk3_0),esk7_0)
    | ~ v3_pre_topc(esk6_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_56,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_40])).

cnf(c_0_57,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0) = k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_15]),c_0_16]),c_0_18])]),c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( r1_tmap_1(esk3_0,X1,k2_tmap_1(X2,X1,X3,esk3_0),X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,X1,X3,X4)
    | ~ r2_hidden(X4,esk6_0)
    | ~ v3_pre_topc(esk6_0,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_37]),c_0_38])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_40])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,X2,esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_55]),c_0_35]),c_0_27]),c_0_29])]),c_0_31])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)
    | r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk3_0,X1,k2_tmap_1(X2,X1,X3,esk3_0),esk7_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X2,X1,X3,esk7_0)
    | ~ v3_pre_topc(esk6_0,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_46])])).

cnf(c_0_63,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_28])]),c_0_30]),c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk4_0,X1,X2,esk7_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_53]),c_0_54]),c_0_55]),c_0_35]),c_0_27]),c_0_29])]),c_0_31])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_23]),c_0_64]),c_0_24]),c_0_25]),c_0_26]),c_0_28])]),c_0_66]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.38  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t84_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.38  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.38  fof(t66_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>((((v3_pre_topc(X5,X2)&r2_hidden(X6,X5))&r1_tarski(X5,u1_struct_0(X4)))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 0.13/0.38  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t84_tmap_1])).
% 0.13/0.38  fof(c_0_8, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_9, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk3_0))&((((v3_pre_topc(esk6_0,esk4_0)&r2_hidden(esk7_0,esk6_0))&r1_tarski(esk6_0,u1_struct_0(esk3_0)))&esk7_0=esk8_0)&((~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0))&(r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.13/0.38  fof(c_0_10, plain, ![X9, X10]:(~v2_pre_topc(X9)|~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|v2_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.38  fof(c_0_11, plain, ![X17, X18, X19, X20, X21]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|(~m1_pre_topc(X19,X17)|(~m1_pre_topc(X20,X17)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X18))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))|(~m1_pre_topc(X20,X19)|k3_tmap_1(X17,X18,X19,X20,X21)=k2_partfun1(u1_struct_0(X19),u1_struct_0(X18),X21,u1_struct_0(X20)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.38  fof(c_0_12, plain, ![X29, X30, X31]:(~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_pre_topc(X30,X29)|(~m1_pre_topc(X31,X30)|m1_pre_topc(X31,X29)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X13, X14, X15, X16]:(v2_struct_0(X13)|~v2_pre_topc(X13)|~l1_pre_topc(X13)|(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|(~v1_funct_1(X15)|~v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))|(~m1_pre_topc(X16,X13)|k2_tmap_1(X13,X14,X15,X16)=k2_partfun1(u1_struct_0(X13),u1_struct_0(X14),X15,u1_struct_0(X16)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_14, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_17, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  fof(c_0_19, plain, ![X22, X23, X24, X25, X26, X27, X28]:((~r1_tmap_1(X23,X22,X24,X27)|r1_tmap_1(X25,X22,k2_tmap_1(X23,X22,X24,X25),X28)|(~v3_pre_topc(X26,X23)|~r2_hidden(X27,X26)|~r1_tarski(X26,u1_struct_0(X25))|X27!=X28)|~m1_subset_1(X28,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X23))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22)))))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(~r1_tmap_1(X25,X22,k2_tmap_1(X23,X22,X24,X25),X28)|r1_tmap_1(X23,X22,X24,X27)|(~v3_pre_topc(X26,X23)|~r2_hidden(X27,X26)|~r1_tarski(X26,u1_struct_0(X25))|X27!=X28)|~m1_subset_1(X28,u1_struct_0(X25))|~m1_subset_1(X27,u1_struct_0(X23))|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X25)|~m1_pre_topc(X25,X23))|(~v1_funct_1(X24)|~v1_funct_2(X24,u1_struct_0(X23),u1_struct_0(X22))|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X22)))))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23))|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_tmap_1])])])])])).
% 0.13/0.38  cnf(c_0_20, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.38  cnf(c_0_21, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16])])).
% 0.13/0.38  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_15]), c_0_16]), c_0_18])])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_32, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~v3_pre_topc(X7,X3)|~r2_hidden(X6,X7)|~r1_tarski(X7,u1_struct_0(X1))|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_33, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)), inference(csr,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk2_0,esk5_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_36, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~r1_tarski(X6,u1_struct_0(X5))|~r2_hidden(X4,X6)|~v3_pre_topc(X6,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X5))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_37, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_28])]), c_0_30])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))=k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.38  cnf(c_0_43, plain, (r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)|v2_struct_0(X5)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,X3,X4)|~v3_pre_topc(X7,X1)|~r2_hidden(X4,X7)|~r1_tarski(X7,u1_struct_0(X5))|X4!=X6|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X5,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(esk3_0,X2,k2_tmap_1(X1,X2,X3,esk3_0),X4)|~r2_hidden(X4,esk6_0)|~v3_pre_topc(esk6_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(esk3_0))|~m1_subset_1(X4,u1_struct_0(X1))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_48, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk4_0,esk3_0,esk5_0)=k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_42])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_50, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,X2,X4,X5)|~r1_tarski(X6,u1_struct_0(X1))|~r2_hidden(X5,X6)|~v3_pre_topc(X6,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X3))|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)), inference(er,[status(thm)],[c_0_43])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (r1_tmap_1(X1,X2,X3,esk7_0)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(esk3_0,X2,k2_tmap_1(X1,X2,X3,esk3_0),esk7_0)|~v3_pre_topc(esk6_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)|r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_47, c_0_40])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0)=k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_15]), c_0_16]), c_0_18])]), c_0_49])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (r1_tmap_1(esk3_0,X1,k2_tmap_1(X2,X1,X3,esk3_0),X4)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X2,X1,X3,X4)|~r2_hidden(X4,esk6_0)|~v3_pre_topc(esk6_0,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X4,u1_struct_0(esk3_0))|~m1_subset_1(X4,u1_struct_0(X2))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_pre_topc(esk3_0,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_37]), c_0_38])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk7_0)|~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_51, c_0_40])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (r1_tmap_1(esk4_0,X1,X2,esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_55]), c_0_35]), c_0_27]), c_0_29])]), c_0_31])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)|r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk3_0,X1,k2_tmap_1(X2,X1,X3,esk3_0),esk7_0)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(X2,X1,X3,esk7_0)|~v3_pre_topc(esk6_0,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(esk7_0,u1_struct_0(X2))|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~v1_funct_1(X3)|~m1_pre_topc(esk3_0,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_46])])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)|~r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_59, c_0_57])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,esk5_0,esk7_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_28])]), c_0_30]), c_0_61])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (r1_tmap_1(esk3_0,X1,k2_tmap_1(esk4_0,X1,X2,esk3_0),esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk4_0,X1,X2,esk7_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_53]), c_0_54]), c_0_55]), c_0_35]), c_0_27]), c_0_29])]), c_0_31])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,k2_tmap_1(esk4_0,esk2_0,esk5_0,esk3_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.13/0.38  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_23]), c_0_64]), c_0_24]), c_0_25]), c_0_26]), c_0_28])]), c_0_66]), c_0_30]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 68
% 0.13/0.38  # Proof object clause steps            : 53
% 0.13/0.38  # Proof object formula steps           : 15
% 0.13/0.38  # Proof object conjectures             : 46
% 0.13/0.38  # Proof object clause conjectures      : 43
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 29
% 0.13/0.38  # Proof object initial formulas used   : 7
% 0.13/0.38  # Proof object generating inferences   : 15
% 0.13/0.38  # Proof object simplifying inferences  : 70
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 7
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 30
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 30
% 0.13/0.38  # Processed clauses                    : 86
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 84
% 0.13/0.38  # Other redundant clauses eliminated   : 2
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 4
% 0.13/0.38  # Generated clauses                    : 25
% 0.13/0.38  # ...of the previous two non-trivial   : 26
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 23
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 2
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 48
% 0.13/0.38  #    Positive orientable unit clauses  : 24
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 19
% 0.13/0.38  # Current number of unprocessed clauses: 0
% 0.13/0.38  # ...number of literals in the above   : 0
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 34
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 411
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 64
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.38  # Unit Clause-clause subsumption calls : 1
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 3
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 4766
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.034 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.039 s
% 0.13/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
