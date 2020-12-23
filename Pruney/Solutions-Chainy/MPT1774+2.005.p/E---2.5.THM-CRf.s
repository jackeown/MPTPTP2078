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
% DateTime   : Thu Dec  3 11:17:48 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   97 (1498 expanded)
%              Number of clauses        :   68 ( 498 expanded)
%              Number of leaves         :   14 ( 361 expanded)
%              Depth                    :   14
%              Number of atoms          :  594 (22086 expanded)
%              Number of equality atoms :   33 ( 974 expanded)
%              Maximal formula depth    :   33 (   7 average)
%              Maximal clause size      :   46 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t85_tmap_1,conjecture,(
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
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( v3_pre_topc(X6,X2)
                                        & r2_hidden(X7,X6)
                                        & r1_tarski(X6,u1_struct_0(X3))
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X1,X5,X7)
                                      <=> r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(t33_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v3_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v3_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t84_tmap_1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(c_0_14,negated_conjecture,(
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
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X2) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X3))
                                     => ( ( v3_pre_topc(X6,X2)
                                          & r2_hidden(X7,X6)
                                          & r1_tarski(X6,u1_struct_0(X3))
                                          & X7 = X8 )
                                       => ( r1_tmap_1(X4,X1,X5,X7)
                                        <=> r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t85_tmap_1])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0))))
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk3_0))
    & v3_pre_topc(esk6_0,esk2_0)
    & r2_hidden(esk7_0,esk6_0)
    & r1_tarski(esk6_0,u1_struct_0(esk3_0))
    & esk7_0 = esk8_0
    & ( ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
      | ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0) )
    & ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
      | r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X31)
      | ~ m1_pre_topc(X34,X31)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X32))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))
      | ~ m1_pre_topc(X34,X33)
      | k3_tmap_1(X31,X32,X33,X34,X35) = k2_partfun1(u1_struct_0(X33),u1_struct_0(X32),X35,u1_struct_0(X34)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_19,plain,(
    ! [X45,X46,X47] :
      ( ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_pre_topc(X46,X45)
      | ~ m1_pre_topc(X47,X46)
      | m1_pre_topc(X47,X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_20,plain,(
    ! [X27,X28,X29,X30] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
      | ~ m1_pre_topc(X30,X27)
      | k2_tmap_1(X27,X28,X29,X30) = k2_partfun1(u1_struct_0(X27),u1_struct_0(X28),X29,u1_struct_0(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_21,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_27,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_23])])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_22]),c_0_23]),c_0_25])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_40,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | m1_pre_topc(X37,X38)
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_pre_topc(X37,X38)
        | r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_42,plain,(
    ! [X23,X24,X25,X26] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
      | ~ m1_pre_topc(X25,X23)
      | ~ v3_pre_topc(X24,X23)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
      | X26 != X24
      | v3_pre_topc(X26,X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

fof(c_0_43,plain,(
    ! [X17,X18,X19] :
      ( ~ l1_pre_topc(X17)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk1_0),esk5_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk1_0,esk5_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_37])]),c_0_38]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_41])).

fof(c_0_51,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55] :
      ( ( ~ r1_tmap_1(X51,X49,X52,X54)
        | r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)
        | ~ v3_pre_topc(X53,X51)
        | ~ r2_hidden(X54,X53)
        | ~ r1_tarski(X53,u1_struct_0(X50))
        | X54 != X55
        | ~ m1_subset_1(X55,u1_struct_0(X50))
        | ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ m1_pre_topc(X50,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49))))
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X48)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) )
      & ( ~ r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)
        | r1_tmap_1(X51,X49,X52,X54)
        | ~ v3_pre_topc(X53,X51)
        | ~ r2_hidden(X54,X53)
        | ~ r1_tarski(X53,u1_struct_0(X50))
        | X54 != X55
        | ~ m1_subset_1(X55,u1_struct_0(X50))
        | ~ m1_subset_1(X54,u1_struct_0(X51))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))
        | ~ m1_pre_topc(X50,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49))))
        | v2_struct_0(X51)
        | ~ m1_pre_topc(X51,X48)
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49)
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).

cnf(c_0_52,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk4_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk1_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_31]),c_0_32]),c_0_33]),c_0_35]),c_0_37])]),c_0_38])).

cnf(c_0_56,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk1_0),esk5_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk4_0,esk1_0,esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_57,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | ~ v3_pre_topc(X8,X4)
    | ~ r2_hidden(X7,X8)
    | ~ r1_tarski(X8,u1_struct_0(X1))
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_59,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0) = k2_tmap_1(esk4_0,esk1_0,esk5_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_48]),c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_22]),c_0_23]),c_0_25])])).

cnf(c_0_64,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r2_hidden(X4,X7)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v3_pre_topc(X7,X1)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_58,c_0_29])])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( v3_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_23])])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_48]),c_0_34])])).

cnf(c_0_68,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk1_0,esk5_0,esk3_0) = k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_34]),c_0_36])]),c_0_39])).

fof(c_0_69,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))
      | v2_struct_0(X42)
      | ~ m1_pre_topc(X42,X40)
      | ~ m1_subset_1(X43,u1_struct_0(X40))
      | ~ m1_subset_1(X44,u1_struct_0(X42))
      | X43 != X44
      | ~ r1_tmap_1(X40,X39,X41,X43)
      | r1_tmap_1(X42,X39,k2_tmap_1(X40,X39,X41,X42),X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

fof(c_0_70,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,X20)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | m1_subset_1(X22,u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tmap_1(X1,X2,X3,esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k3_tmap_1(X4,X2,X1,X5,X3),esk7_0)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v3_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X5))
    | ~ r1_tarski(esk6_0,u1_struct_0(X5)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_22])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_76,negated_conjecture,
    ( k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0) = k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_62,c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_78,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_80,negated_conjecture,
    ( r1_tmap_1(esk4_0,X1,X2,esk7_0)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | ~ r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,esk4_0,X3,X2),esk7_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(esk4_0,X4)
    | ~ m1_pre_topc(X3,esk4_0)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X3))
    | ~ r1_tarski(esk6_0,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_67]),c_0_73])]),c_0_39])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0) = k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_22]),c_0_23]),c_0_25])]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_85,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_78]),c_0_79])).

cnf(c_0_86,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk1_0,k3_tmap_1(X1,esk1_0,esk4_0,X2,esk5_0),esk7_0)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,esk4_0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk7_0,u1_struct_0(X2))
    | ~ r1_tarski(esk6_0,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_31]),c_0_32]),c_0_33]),c_0_35]),c_0_37])]),c_0_38])).

cnf(c_0_87,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_83,c_0_75])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_84,c_0_75])).

cnf(c_0_91,negated_conjecture,
    ( r1_tmap_1(X1,esk1_0,k2_tmap_1(esk4_0,esk1_0,esk5_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_31]),c_0_32]),c_0_34]),c_0_33]),c_0_36]),c_0_35]),c_0_37])]),c_0_38]),c_0_39])).

cnf(c_0_92,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_63]),c_0_48]),c_0_34]),c_0_36]),c_0_88]),c_0_45])]),c_0_39]),c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_82])).

cnf(c_0_94,negated_conjecture,
    ( r1_tmap_1(X1,esk1_0,k2_tmap_1(esk4_0,esk1_0,esk5_0,X1),esk7_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_92])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_88]),c_0_68]),c_0_48])]),c_0_95]),c_0_89]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.030 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t85_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.39  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.13/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.39  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.39  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 0.13/0.39  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.13/0.39  fof(t84_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.13/0.39  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.13/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.13/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t85_tmap_1])).
% 0.13/0.39  fof(c_0_15, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk3_0))&((((v3_pre_topc(esk6_0,esk2_0)&r2_hidden(esk7_0,esk6_0))&r1_tarski(esk6_0,u1_struct_0(esk3_0)))&esk7_0=esk8_0)&((~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0))&(r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.13/0.39  fof(c_0_17, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.39  fof(c_0_18, plain, ![X31, X32, X33, X34, X35]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_pre_topc(X33,X31)|(~m1_pre_topc(X34,X31)|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X32))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X32))))|(~m1_pre_topc(X34,X33)|k3_tmap_1(X31,X32,X33,X34,X35)=k2_partfun1(u1_struct_0(X33),u1_struct_0(X32),X35,u1_struct_0(X34)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.39  fof(c_0_19, plain, ![X45, X46, X47]:(~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_pre_topc(X46,X45)|(~m1_pre_topc(X47,X46)|m1_pre_topc(X47,X45)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.13/0.39  fof(c_0_20, plain, ![X27, X28, X29, X30]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))|(~m1_pre_topc(X30,X27)|k2_tmap_1(X27,X28,X29,X30)=k2_partfun1(u1_struct_0(X27),u1_struct_0(X28),X29,u1_struct_0(X30)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.39  cnf(c_0_21, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_24, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_26, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.39  fof(c_0_27, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_29, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_30, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_33, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_23])])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_22]), c_0_23]), c_0_25])])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  fof(c_0_40, plain, ![X36, X37, X38]:((~r1_tarski(u1_struct_0(X37),u1_struct_0(X38))|m1_pre_topc(X37,X38)|~m1_pre_topc(X38,X36)|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(~m1_pre_topc(X37,X38)|r1_tarski(u1_struct_0(X37),u1_struct_0(X38))|~m1_pre_topc(X38,X36)|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.39  cnf(c_0_41, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.39  fof(c_0_42, plain, ![X23, X24, X25, X26]:(~l1_pre_topc(X23)|(~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(~m1_pre_topc(X25,X23)|(~v3_pre_topc(X24,X23)|(~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))|(X26!=X24|v3_pre_topc(X26,X25))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.13/0.39  fof(c_0_43, plain, ![X17, X18, X19]:(~l1_pre_topc(X17)|(~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X17)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.13/0.39  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_46, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk1_0),esk5_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk1_0,esk5_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_37])]), c_0_38]), c_0_39])).
% 0.13/0.39  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_49, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.39  cnf(c_0_50, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_41])).
% 0.13/0.39  fof(c_0_51, plain, ![X48, X49, X50, X51, X52, X53, X54, X55]:((~r1_tmap_1(X51,X49,X52,X54)|r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)|(~v3_pre_topc(X53,X51)|~r2_hidden(X54,X53)|~r1_tarski(X53,u1_struct_0(X50))|X54!=X55)|~m1_subset_1(X55,u1_struct_0(X50))|~m1_subset_1(X54,u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|~m1_pre_topc(X50,X51)|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49)))))|(v2_struct_0(X51)|~m1_pre_topc(X51,X48))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))&(~r1_tmap_1(X50,X49,k3_tmap_1(X48,X49,X51,X50,X52),X55)|r1_tmap_1(X51,X49,X52,X54)|(~v3_pre_topc(X53,X51)|~r2_hidden(X54,X53)|~r1_tarski(X53,u1_struct_0(X50))|X54!=X55)|~m1_subset_1(X55,u1_struct_0(X50))|~m1_subset_1(X54,u1_struct_0(X51))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X51)))|~m1_pre_topc(X50,X51)|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X49))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X49)))))|(v2_struct_0(X51)|~m1_pre_topc(X51,X48))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).
% 0.13/0.39  cnf(c_0_52, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.13/0.39  cnf(c_0_53, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk4_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk1_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk4_0)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_31]), c_0_32]), c_0_33]), c_0_35]), c_0_37])]), c_0_38])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk1_0),esk5_0,u1_struct_0(esk3_0))=k2_tmap_1(esk4_0,esk1_0,esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.13/0.39  cnf(c_0_57, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.13/0.39  cnf(c_0_58, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~v3_pre_topc(X8,X4)|~r2_hidden(X7,X8)|~r1_tarski(X8,u1_struct_0(X1))|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_59, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_53])).
% 0.13/0.39  cnf(c_0_60, negated_conjecture, (v3_pre_topc(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0)=k2_tmap_1(esk4_0,esk1_0,esk5_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_48]), c_0_56])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (m1_pre_topc(esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_22]), c_0_23]), c_0_25])])).
% 0.13/0.39  cnf(c_0_64, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r2_hidden(X4,X7)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v3_pre_topc(X7,X1)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_58, c_0_29])])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_66, negated_conjecture, (v3_pre_topc(esk6_0,X1)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_23])])).
% 0.13/0.39  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_48]), c_0_34])])).
% 0.13/0.39  cnf(c_0_68, negated_conjecture, (k2_tmap_1(esk4_0,esk1_0,esk5_0,esk3_0)=k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_34]), c_0_36])]), c_0_39])).
% 0.13/0.39  fof(c_0_69, plain, ![X39, X40, X41, X42, X43, X44]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(~v1_funct_1(X41)|~v1_funct_2(X41,u1_struct_0(X40),u1_struct_0(X39))|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X39))))|(v2_struct_0(X42)|~m1_pre_topc(X42,X40)|(~m1_subset_1(X43,u1_struct_0(X40))|(~m1_subset_1(X44,u1_struct_0(X42))|(X43!=X44|~r1_tmap_1(X40,X39,X41,X43)|r1_tmap_1(X42,X39,k2_tmap_1(X40,X39,X41,X42),X44)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.13/0.39  fof(c_0_70, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X20)|(~m1_subset_1(X22,u1_struct_0(X21))|m1_subset_1(X22,u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.13/0.39  cnf(c_0_71, negated_conjecture, (r1_tmap_1(X1,X2,X3,esk7_0)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k3_tmap_1(X4,X2,X1,X5,X3),esk7_0)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v3_pre_topc(esk6_0,X1)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X4)|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(esk7_0,u1_struct_0(X5))|~r1_tarski(esk6_0,u1_struct_0(X5))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.13/0.39  cnf(c_0_72, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_22])])).
% 0.13/0.39  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_75, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_76, negated_conjecture, (k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0)=k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0)|v2_struct_0(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_62, c_0_68])).
% 0.13/0.39  cnf(c_0_77, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_78, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.13/0.39  cnf(c_0_79, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.13/0.39  cnf(c_0_80, negated_conjecture, (r1_tmap_1(esk4_0,X1,X2,esk7_0)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|~r1_tmap_1(X3,X1,k3_tmap_1(X4,X1,esk4_0,X3,X2),esk7_0)|~v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))|~v1_funct_1(X2)|~m1_pre_topc(esk4_0,X4)|~m1_pre_topc(X3,esk4_0)|~l1_pre_topc(X4)|~l1_pre_topc(X1)|~v2_pre_topc(X4)|~v2_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))|~m1_subset_1(esk7_0,u1_struct_0(X3))|~r1_tarski(esk6_0,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_67]), c_0_73])]), c_0_39])).
% 0.13/0.39  cnf(c_0_81, negated_conjecture, (r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.13/0.39  cnf(c_0_82, negated_conjecture, (k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0)=k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_22]), c_0_23]), c_0_25])]), c_0_77])).
% 0.13/0.39  cnf(c_0_83, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_84, negated_conjecture, (~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_85, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_78]), c_0_79])).
% 0.13/0.39  cnf(c_0_86, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk1_0,k3_tmap_1(X1,esk1_0,esk4_0,X2,esk5_0),esk7_0)|~m1_pre_topc(esk4_0,X1)|~m1_pre_topc(X2,esk4_0)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk7_0,u1_struct_0(X2))|~r1_tarski(esk6_0,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_31]), c_0_32]), c_0_33]), c_0_35]), c_0_37])]), c_0_38])).
% 0.13/0.39  cnf(c_0_87, negated_conjecture, (r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.13/0.39  cnf(c_0_88, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_83, c_0_75])).
% 0.13/0.39  cnf(c_0_89, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_90, negated_conjecture, (~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_84, c_0_75])).
% 0.13/0.39  cnf(c_0_91, negated_conjecture, (r1_tmap_1(X1,esk1_0,k2_tmap_1(esk4_0,esk1_0,esk5_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk4_0,esk1_0,esk5_0,X2)|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_31]), c_0_32]), c_0_34]), c_0_33]), c_0_36]), c_0_35]), c_0_37])]), c_0_38]), c_0_39])).
% 0.13/0.39  cnf(c_0_92, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_63]), c_0_48]), c_0_34]), c_0_36]), c_0_88]), c_0_45])]), c_0_39]), c_0_89])).
% 0.13/0.39  cnf(c_0_93, negated_conjecture, (~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_90, c_0_82])).
% 0.13/0.39  cnf(c_0_94, negated_conjecture, (r1_tmap_1(X1,esk1_0,k2_tmap_1(esk4_0,esk1_0,esk5_0,X1),esk7_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_subset_1(esk7_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.13/0.39  cnf(c_0_95, negated_conjecture, (~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk4_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_92])])).
% 0.13/0.39  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_88]), c_0_68]), c_0_48])]), c_0_95]), c_0_89]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 97
% 0.13/0.39  # Proof object clause steps            : 68
% 0.13/0.39  # Proof object formula steps           : 29
% 0.13/0.39  # Proof object conjectures             : 52
% 0.13/0.39  # Proof object clause conjectures      : 49
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 34
% 0.13/0.39  # Proof object initial formulas used   : 14
% 0.13/0.39  # Proof object generating inferences   : 22
% 0.13/0.39  # Proof object simplifying inferences  : 87
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 14
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 41
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 41
% 0.13/0.39  # Processed clauses                    : 163
% 0.13/0.39  # ...of these trivial                  : 3
% 0.13/0.39  # ...subsumed                          : 3
% 0.13/0.39  # ...remaining for further processing  : 157
% 0.13/0.39  # Other redundant clauses eliminated   : 6
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 9
% 0.13/0.39  # Generated clauses                    : 131
% 0.13/0.39  # ...of the previous two non-trivial   : 92
% 0.13/0.39  # Contextual simplify-reflections      : 6
% 0.13/0.39  # Paramodulations                      : 125
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 6
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 102
% 0.13/0.39  #    Positive orientable unit clauses  : 46
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 5
% 0.13/0.39  #    Non-unit-clauses                  : 51
% 0.13/0.39  # Current number of unprocessed clauses: 5
% 0.13/0.39  # ...number of literals in the above   : 80
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 49
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 1975
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 158
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 9
% 0.13/0.39  # Unit Clause-clause subsumption calls : 39
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 32
% 0.13/0.39  # BW rewrite match successes           : 4
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 8691
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.045 s
% 0.13/0.39  # System time              : 0.003 s
% 0.13/0.39  # Total time               : 0.048 s
% 0.13/0.39  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
