%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t21_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:11 EDT 2019

% Result     : Theorem 152.44s
% Output     : CNFRefutation 152.44s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 172 expanded)
%              Number of clauses        :   40 (  57 expanded)
%              Number of leaves         :    7 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :  406 (2163 expanded)
%              Number of equality atoms :   26 ( 238 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal clause size      :   60 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',t4_subset)).

fof(t20_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ( ( X5 = X4
                              & X6 = X4 )
                           => ! [X7] :
                                ( m1_connsp_2(X7,X2,X5)
                               => ! [X8] :
                                    ( m1_connsp_2(X8,X3,X6)
                                   => ? [X9] :
                                        ( m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
                                        & v3_pre_topc(X9,k1_tsep_1(X1,X2,X3))
                                        & r2_hidden(X4,X9)
                                        & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',t20_tmap_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',cc1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',dt_k1_tsep_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',dt_m1_pre_topc)).

fof(t21_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ( ( X5 = X4
                              & X6 = X4 )
                           => ! [X7] :
                                ( m1_connsp_2(X7,X2,X5)
                               => ! [X8] :
                                    ( m1_connsp_2(X8,X3,X6)
                                   => ? [X9] :
                                        ( m1_connsp_2(X9,k1_tsep_1(X1,X2,X3),X4)
                                        & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t21_tmap_1.p',t21_tmap_1)).

fof(c_0_7,plain,(
    ! [X72,X73,X74] :
      ( v2_struct_0(X72)
      | ~ v2_pre_topc(X72)
      | ~ l1_pre_topc(X72)
      | ~ m1_subset_1(X73,k1_zfmisc_1(u1_struct_0(X72)))
      | ~ m1_subset_1(X74,u1_struct_0(X72))
      | ~ v3_pre_topc(X73,X72)
      | ~ r2_hidden(X74,X73)
      | m1_connsp_2(X73,X72,X74) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_8,plain,(
    ! [X69,X70,X71] :
      ( ~ r2_hidden(X69,X70)
      | ~ m1_subset_1(X70,k1_zfmisc_1(X71))
      | m1_subset_1(X69,X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_9,plain,(
    ! [X56,X57,X58,X59,X60,X61,X62,X63] :
      ( ( m1_subset_1(esk14_8(X56,X57,X58,X59,X60,X61,X62,X63),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X56,X57,X58))))
        | ~ m1_connsp_2(X63,X58,X61)
        | ~ m1_connsp_2(X62,X57,X60)
        | X60 != X59
        | X61 != X59
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X57))
        | ~ m1_subset_1(X59,u1_struct_0(k1_tsep_1(X56,X57,X58)))
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( v3_pre_topc(esk14_8(X56,X57,X58,X59,X60,X61,X62,X63),k1_tsep_1(X56,X57,X58))
        | ~ m1_connsp_2(X63,X58,X61)
        | ~ m1_connsp_2(X62,X57,X60)
        | X60 != X59
        | X61 != X59
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X57))
        | ~ m1_subset_1(X59,u1_struct_0(k1_tsep_1(X56,X57,X58)))
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( r2_hidden(X59,esk14_8(X56,X57,X58,X59,X60,X61,X62,X63))
        | ~ m1_connsp_2(X63,X58,X61)
        | ~ m1_connsp_2(X62,X57,X60)
        | X60 != X59
        | X61 != X59
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X57))
        | ~ m1_subset_1(X59,u1_struct_0(k1_tsep_1(X56,X57,X58)))
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) )
      & ( r1_tarski(esk14_8(X56,X57,X58,X59,X60,X61,X62,X63),k2_xboole_0(X62,X63))
        | ~ m1_connsp_2(X63,X58,X61)
        | ~ m1_connsp_2(X62,X57,X60)
        | X60 != X59
        | X61 != X59
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X57))
        | ~ m1_subset_1(X59,u1_struct_0(k1_tsep_1(X56,X57,X58)))
        | v2_struct_0(X58)
        | ~ m1_pre_topc(X58,X56)
        | v2_struct_0(X57)
        | ~ m1_pre_topc(X57,X56)
        | v2_struct_0(X56)
        | ~ v2_pre_topc(X56)
        | ~ l1_pre_topc(X56) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t20_tmap_1])])])])])])).

fof(c_0_10,plain,(
    ! [X83,X84] :
      ( ~ v2_pre_topc(X83)
      | ~ l1_pre_topc(X83)
      | ~ m1_pre_topc(X84,X83)
      | v2_pre_topc(X84) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_11,plain,(
    ! [X29,X30,X31] :
      ( ( ~ v2_struct_0(k1_tsep_1(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29) )
      & ( v1_pre_topc(k1_tsep_1(X29,X30,X31))
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29) )
      & ( m1_pre_topc(k1_tsep_1(X29,X30,X31),X29)
        | v2_struct_0(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X30)
        | ~ m1_pre_topc(X30,X29)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_12,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | l1_pre_topc(X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ( ( X5 = X4
                                & X6 = X4 )
                             => ! [X7] :
                                  ( m1_connsp_2(X7,X2,X5)
                                 => ! [X8] :
                                      ( m1_connsp_2(X8,X3,X6)
                                     => ? [X9] :
                                          ( m1_connsp_2(X9,k1_tsep_1(X1,X2,X3),X4)
                                          & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t21_tmap_1])).

cnf(c_0_14,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( m1_subset_1(esk14_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X8,X3,X6)
    | ~ m1_connsp_2(X7,X2,X5)
    | X5 != X4
    | X6 != X4
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v3_pre_topc(esk14_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X8,X3,X6)
    | ~ m1_connsp_2(X7,X2,X5)
    | X5 != X4
    | X6 != X4
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_21,negated_conjecture,(
    ! [X18] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk1_0)
      & m1_subset_1(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
      & m1_subset_1(esk5_0,u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
      & esk5_0 = esk4_0
      & esk6_0 = esk4_0
      & m1_connsp_2(esk7_0,esk2_0,esk5_0)
      & m1_connsp_2(esk8_0,esk3_0,esk6_0)
      & ( ~ m1_connsp_2(X18,k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
        | ~ r1_tarski(X18,k2_xboole_0(esk7_0,esk8_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

cnf(c_0_22,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk14_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_16])])).

cnf(c_0_24,plain,
    ( v2_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( l1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_26,plain,
    ( v3_pre_topc(esk14_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( ~ m1_connsp_2(X1,k1_tsep_1(esk1_0,esk2_0,esk3_0),esk4_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_connsp_2(esk14_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_tsep_1(X1,X2,X3),X7)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X7,esk14_8(X1,X2,X3,X4,X4,X4,X5,X6))
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_37,plain,
    ( r1_tarski(esk14_8(X1,X2,X3,X4,X5,X6,X7,X8),k2_xboole_0(X7,X8))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X8,X3,X6)
    | ~ m1_connsp_2(X7,X2,X5)
    | X5 != X4
    | X6 != X4
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk14_8(esk1_0,esk2_0,esk3_0,X1,X1,X1,X2,X3))
    | ~ r1_tarski(esk14_8(esk1_0,esk2_0,esk3_0,X1,X1,X1,X2,X3),k2_xboole_0(esk7_0,esk8_0))
    | ~ m1_connsp_2(X3,esk3_0,X1)
    | ~ m1_connsp_2(X2,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_39,plain,
    ( r1_tarski(esk14_8(X1,X2,X3,X4,X4,X4,X5,X6),k2_xboole_0(X5,X6))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_37])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,esk14_8(X2,X3,X4,X1,X5,X6,X7,X8))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X8,X4,X6)
    | ~ m1_connsp_2(X7,X3,X5)
    | X5 != X1
    | X6 != X1
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,negated_conjecture,
    ( m1_connsp_2(esk8_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_43,negated_conjecture,
    ( m1_connsp_2(esk7_0,esk2_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_hidden(esk4_0,esk14_8(esk1_0,esk2_0,esk3_0,X1,X1,X1,esk7_0,esk8_0))
    | ~ m1_connsp_2(esk8_0,esk3_0,X1)
    | ~ m1_connsp_2(esk7_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_36]),c_0_35]),c_0_34])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,esk14_8(X2,X3,X4,X1,X1,X1,X5,X6))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X6,X4,X1)
    | ~ m1_connsp_2(X5,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_40])])).

cnf(c_0_49,negated_conjecture,
    ( m1_connsp_2(esk8_0,esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( m1_connsp_2(esk7_0,esk2_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(k1_tsep_1(esk1_0,esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52]),c_0_53]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_36]),c_0_35]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
