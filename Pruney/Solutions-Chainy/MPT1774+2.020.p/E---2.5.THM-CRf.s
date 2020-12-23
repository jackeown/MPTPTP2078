%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:51 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 430 expanded)
%              Number of clauses        :   49 ( 146 expanded)
%              Number of leaves         :    8 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  427 (6436 expanded)
%              Number of equality atoms :   14 ( 263 expanded)
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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

fof(c_0_11,plain,(
    ! [X16,X17,X18,X19] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | ~ m1_pre_topc(X18,X16)
      | ~ v3_pre_topc(X17,X16)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | X19 != X17
      | v3_pre_topc(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).

fof(c_0_12,plain,(
    ! [X13,X14,X15] :
      ( ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_13,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X30,X31,X32,X33,X34,X35,X36,X37] :
      ( ( ~ r1_tmap_1(X33,X31,X34,X36)
        | r1_tmap_1(X32,X31,k3_tmap_1(X30,X31,X33,X32,X34),X37)
        | ~ v3_pre_topc(X35,X33)
        | ~ r2_hidden(X36,X35)
        | ~ r1_tarski(X35,u1_struct_0(X32))
        | X36 != X37
        | ~ m1_subset_1(X37,u1_struct_0(X32))
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X32,X33)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X31))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ r1_tmap_1(X32,X31,k3_tmap_1(X30,X31,X33,X32,X34),X37)
        | r1_tmap_1(X33,X31,X34,X36)
        | ~ v3_pre_topc(X35,X33)
        | ~ r2_hidden(X36,X35)
        | ~ r1_tarski(X35,u1_struct_0(X32))
        | X36 != X37
        | ~ m1_subset_1(X37,u1_struct_0(X32))
        | ~ m1_subset_1(X36,u1_struct_0(X33))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_pre_topc(X32,X33)
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X31))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31))))
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30)
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).

fof(c_0_18,plain,(
    ! [X20,X21,X22] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | ~ m1_pre_topc(X22,X21)
      | m1_pre_topc(X22,X20) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_19,plain,
    ( v3_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( v3_pre_topc(X1,X2)
    | ~ v3_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]),c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r2_hidden(X4,X7)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ v3_pre_topc(X7,X1)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X7,u1_struct_0(X6))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_25,c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( v3_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_15])])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

fof(c_0_35,plain,(
    ! [X23,X24,X25,X26,X27,X28,X29] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ m1_pre_topc(X25,X23)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X23)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X24))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))
      | ~ m1_subset_1(X28,u1_struct_0(X25))
      | ~ m1_subset_1(X29,u1_struct_0(X26))
      | X28 != X29
      | ~ m1_pre_topc(X26,X25)
      | ~ r1_tmap_1(X25,X24,X27,X28)
      | r1_tmap_1(X26,X24,k3_tmap_1(X23,X24,X25,X26,X27),X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).

cnf(c_0_36,negated_conjecture,
    ( r1_tmap_1(X1,X2,X3,esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k3_tmap_1(X4,X2,X1,X5,X3),esk7_0)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ v3_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(esk6_0,u1_struct_0(X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X5)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_14]),c_0_34])])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,esk1_0,k3_tmap_1(X2,esk1_0,esk4_0,X1,esk5_0),esk7_0)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(esk6_0,u1_struct_0(X1))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_41]),c_0_42]),c_0_34]),c_0_43])]),c_0_44]),c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_52,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_53,plain,
    ( r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X4,X2,X5,X6)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_pre_topc(X4,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X4)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48,c_0_26])])).

cnf(c_0_54,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_24]),c_0_21]),c_0_50])]),c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_47])).

cnf(c_0_56,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( r1_tmap_1(X1,esk1_0,k3_tmap_1(X2,esk1_0,esk4_0,X1,esk5_0),X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_37]),c_0_38]),c_0_39]),c_0_41]),c_0_42])]),c_0_45]),c_0_44])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_14]),c_0_15])]),c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)
    | ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(X1,esk1_0,k3_tmap_1(X2,esk1_0,esk4_0,X1,esk5_0),esk7_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(esk7_0,u1_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_43])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_60,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_21]),c_0_50])]),c_0_51])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_14]),c_0_56]),c_0_15])]),c_0_64]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.14/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t85_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 0.14/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.14/0.39  fof(t33_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v3_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v3_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 0.14/0.39  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 0.14/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.39  fof(t84_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X4)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 0.14/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.14/0.39  fof(t81_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((X6=X7&m1_pre_topc(X4,X3))&r1_tmap_1(X3,X2,X5,X6))=>r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 0.14/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X2)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>((((v3_pre_topc(X6,X2)&r2_hidden(X7,X6))&r1_tarski(X6,u1_struct_0(X3)))&X7=X8)=>(r1_tmap_1(X4,X1,X5,X7)<=>r1_tmap_1(X3,X1,k3_tmap_1(X2,X1,X4,X3,X5),X8))))))))))))), inference(assume_negation,[status(cth)],[t85_tmap_1])).
% 0.14/0.39  fof(c_0_9, plain, ![X11, X12]:(~l1_pre_topc(X11)|(~m1_pre_topc(X12,X11)|l1_pre_topc(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.14/0.39  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0)))))&(m1_pre_topc(esk3_0,esk4_0)&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk3_0))&((((v3_pre_topc(esk6_0,esk2_0)&r2_hidden(esk7_0,esk6_0))&r1_tarski(esk6_0,u1_struct_0(esk3_0)))&esk7_0=esk8_0)&((~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0))&(r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0))))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).
% 0.14/0.39  fof(c_0_11, plain, ![X16, X17, X18, X19]:(~l1_pre_topc(X16)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(~m1_pre_topc(X18,X16)|(~v3_pre_topc(X17,X16)|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(X19!=X17|v3_pre_topc(X19,X18))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t33_tops_2])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X13, X14, X15]:(~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 0.14/0.39  cnf(c_0_13, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  fof(c_0_16, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.39  fof(c_0_17, plain, ![X30, X31, X32, X33, X34, X35, X36, X37]:((~r1_tmap_1(X33,X31,X34,X36)|r1_tmap_1(X32,X31,k3_tmap_1(X30,X31,X33,X32,X34),X37)|(~v3_pre_topc(X35,X33)|~r2_hidden(X36,X35)|~r1_tarski(X35,u1_struct_0(X32))|X36!=X37)|~m1_subset_1(X37,u1_struct_0(X32))|~m1_subset_1(X36,u1_struct_0(X33))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X32,X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31)))))|(v2_struct_0(X33)|~m1_pre_topc(X33,X30))|(v2_struct_0(X32)|~m1_pre_topc(X32,X30))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~r1_tmap_1(X32,X31,k3_tmap_1(X30,X31,X33,X32,X34),X37)|r1_tmap_1(X33,X31,X34,X36)|(~v3_pre_topc(X35,X33)|~r2_hidden(X36,X35)|~r1_tarski(X35,u1_struct_0(X32))|X36!=X37)|~m1_subset_1(X37,u1_struct_0(X32))|~m1_subset_1(X36,u1_struct_0(X33))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_pre_topc(X32,X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X33),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X31)))))|(v2_struct_0(X33)|~m1_pre_topc(X33,X30))|(v2_struct_0(X32)|~m1_pre_topc(X32,X30))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t84_tmap_1])])])])])).
% 0.14/0.39  fof(c_0_18, plain, ![X20, X21, X22]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|(~m1_pre_topc(X22,X21)|m1_pre_topc(X22,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.14/0.39  cnf(c_0_19, plain, (v3_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v3_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_20, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15])])).
% 0.14/0.39  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (r1_tarski(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_25, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~v3_pre_topc(X8,X4)|~r2_hidden(X7,X8)|~r1_tarski(X8,u1_struct_0(X1))|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_26, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_27, plain, (v3_pre_topc(X1,X2)|~v3_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_19]), c_0_20])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (v3_pre_topc(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.39  cnf(c_0_31, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r2_hidden(X4,X7)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~v3_pre_topc(X7,X1)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~r1_tarski(X7,u1_struct_0(X6))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_25, c_0_26])])).
% 0.14/0.39  cnf(c_0_32, negated_conjecture, (r2_hidden(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (v3_pre_topc(esk6_0,X1)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_15])])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  fof(c_0_35, plain, ![X23, X24, X25, X26, X27, X28, X29]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~m1_pre_topc(X25,X23)|(v2_struct_0(X26)|~m1_pre_topc(X26,X23)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X24))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))|(~m1_subset_1(X28,u1_struct_0(X25))|(~m1_subset_1(X29,u1_struct_0(X26))|(X28!=X29|~m1_pre_topc(X26,X25)|~r1_tmap_1(X25,X24,X27,X28)|r1_tmap_1(X26,X24,k3_tmap_1(X23,X24,X25,X26,X27),X29))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t81_tmap_1])])])])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (r1_tmap_1(X1,X2,X3,esk7_0)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k3_tmap_1(X4,X2,X1,X5,X3),esk7_0)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~v2_pre_topc(X4)|~v2_pre_topc(X2)|~v3_pre_topc(esk6_0,X1)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X4)|~l1_pre_topc(X2)|~r1_tarski(esk6_0,u1_struct_0(X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk7_0,u1_struct_0(X1))|~m1_subset_1(esk7_0,u1_struct_0(X5))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (v3_pre_topc(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_14]), c_0_34])])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_47, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r1_tmap_1(X4,X2,k3_tmap_1(X1,X2,X3,X4,X5),X7)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,u1_struct_0(X4))|X6!=X7|~m1_pre_topc(X4,X3)|~r1_tmap_1(X3,X2,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,esk1_0,k3_tmap_1(X2,esk1_0,esk4_0,X1,esk5_0),esk7_0)|~v2_pre_topc(X2)|~m1_pre_topc(esk4_0,X2)|~m1_pre_topc(X1,esk4_0)|~l1_pre_topc(X2)|~r1_tarski(esk6_0,u1_struct_0(X1))|~m1_subset_1(esk7_0,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_41]), c_0_42]), c_0_34]), c_0_43])]), c_0_44]), c_0_45])).
% 0.14/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_53, plain, (r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X4,X2,X5,X6)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~v1_funct_1(X5)|~v2_pre_topc(X2)|~v2_pre_topc(X3)|~m1_pre_topc(X1,X4)|~m1_pre_topc(X4,X3)|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X4))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_48, c_0_26])])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_24]), c_0_21]), c_0_50])]), c_0_51])).
% 0.14/0.39  cnf(c_0_55, negated_conjecture, (r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_52, c_0_47])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_58, negated_conjecture, (r1_tmap_1(X1,esk1_0,k3_tmap_1(X2,esk1_0,esk4_0,X1,esk5_0),X3)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(esk4_0,esk1_0,esk5_0,X3)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(esk4_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(esk4_0))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_37]), c_0_38]), c_0_39]), c_0_41]), c_0_42])]), c_0_45]), c_0_44])).
% 0.14/0.39  cnf(c_0_59, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_14]), c_0_15])]), c_0_57])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)|~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (r1_tmap_1(X1,esk1_0,k3_tmap_1(X2,esk1_0,esk4_0,X1,esk5_0),esk7_0)|v2_struct_0(X2)|v2_struct_0(X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(esk4_0,X2)|~l1_pre_topc(X2)|~m1_subset_1(esk7_0,u1_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_43])])).
% 0.14/0.39  cnf(c_0_62, negated_conjecture, (~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|~r1_tmap_1(esk4_0,esk1_0,esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_60, c_0_47])).
% 0.14/0.39  cnf(c_0_63, negated_conjecture, (r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(X1,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_21]), c_0_50])]), c_0_51])).
% 0.14/0.39  cnf(c_0_64, negated_conjecture, (~r1_tmap_1(esk3_0,esk1_0,k3_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0,esk5_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_59])])).
% 0.14/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_14]), c_0_56]), c_0_15])]), c_0_64]), c_0_57]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 66
% 0.14/0.39  # Proof object clause steps            : 49
% 0.14/0.39  # Proof object formula steps           : 17
% 0.14/0.39  # Proof object conjectures             : 42
% 0.14/0.39  # Proof object clause conjectures      : 39
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 28
% 0.14/0.39  # Proof object initial formulas used   : 8
% 0.14/0.39  # Proof object generating inferences   : 14
% 0.14/0.39  # Proof object simplifying inferences  : 55
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 8
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 32
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 32
% 0.14/0.39  # Processed clauses                    : 94
% 0.14/0.39  # ...of these trivial                  : 1
% 0.14/0.39  # ...subsumed                          : 1
% 0.14/0.39  # ...remaining for further processing  : 92
% 0.14/0.39  # Other redundant clauses eliminated   : 4
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 4
% 0.14/0.39  # Generated clauses                    : 41
% 0.14/0.39  # ...of the previous two non-trivial   : 33
% 0.14/0.39  # Contextual simplify-reflections      : 4
% 0.14/0.39  # Paramodulations                      : 37
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 4
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 53
% 0.14/0.39  #    Positive orientable unit clauses  : 27
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 5
% 0.14/0.39  #    Non-unit-clauses                  : 21
% 0.14/0.39  # Current number of unprocessed clauses: 0
% 0.14/0.39  # ...number of literals in the above   : 0
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 35
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 941
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 66
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.39  # Unit Clause-clause subsumption calls : 19
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 6
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 4808
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.034 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.039 s
% 0.14/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
