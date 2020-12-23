%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:53 EST 2020

% Result     : Theorem 0.46s
% Output     : CNFRefutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 408 expanded)
%              Number of clauses        :   49 ( 132 expanded)
%              Number of leaves         :    6 (  95 expanded)
%              Depth                    :   13
%              Number of atoms          :  416 (4843 expanded)
%              Number of equality atoms :   26 ( 580 expanded)
%              Maximal formula depth    :   27 (   7 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(fc1_tmap_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & v2_pre_topc(k1_tsep_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,plain,(
    ! [X21,X22,X23,X24,X25,X26,X27,X28] :
      ( ( m1_subset_1(esk1_8(X21,X22,X23,X24,X25,X26,X27,X28),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X22,X23))))
        | ~ m1_connsp_2(X28,X23,X26)
        | ~ m1_connsp_2(X27,X22,X25)
        | X25 != X24
        | X26 != X24
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(esk1_8(X21,X22,X23,X24,X25,X26,X27,X28),k1_tsep_1(X21,X22,X23))
        | ~ m1_connsp_2(X28,X23,X26)
        | ~ m1_connsp_2(X27,X22,X25)
        | X25 != X24
        | X26 != X24
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(X24,esk1_8(X21,X22,X23,X24,X25,X26,X27,X28))
        | ~ m1_connsp_2(X28,X23,X26)
        | ~ m1_connsp_2(X27,X22,X25)
        | X25 != X24
        | X26 != X24
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(esk1_8(X21,X22,X23,X24,X25,X26,X27,X28),k2_xboole_0(X27,X28))
        | ~ m1_connsp_2(X28,X23,X26)
        | ~ m1_connsp_2(X27,X22,X25)
        | X25 != X24
        | X26 != X24
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t20_tmap_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ! [X38] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))
      & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
      & esk6_0 = esk5_0
      & esk7_0 = esk5_0
      & m1_connsp_2(esk8_0,esk3_0,esk6_0)
      & m1_connsp_2(esk9_0,esk4_0,esk7_0)
      & ( ~ m1_connsp_2(X38,k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)
        | ~ r1_tarski(X38,k2_xboole_0(esk8_0,esk9_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).

cnf(c_0_9,plain,
    ( m1_subset_1(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk6_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v2_struct_0(k1_tsep_1(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) )
      & ( v1_pre_topc(k1_tsep_1(X15,X16,X17))
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) )
      & ( m1_pre_topc(k1_tsep_1(X15,X16,X17),X15)
        | v2_struct_0(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | v2_struct_0(X17)
        | ~ m1_pre_topc(X17,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_27,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v2_struct_0(k1_tsep_1(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18) )
      & ( v1_pre_topc(k1_tsep_1(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18) )
      & ( v2_pre_topc(k1_tsep_1(X18,X19,X20))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | v2_struct_0(X19)
        | ~ m1_pre_topc(X19,X18)
        | v2_struct_0(X20)
        | ~ m1_pre_topc(X20,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tmap_1])])])])).

cnf(c_0_28,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( m1_connsp_2(esk8_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,plain,
    ( v2_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_33,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | l1_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_34,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk2_0,X1,esk4_0),esk2_0)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_20]),c_0_22])]),c_0_25]),c_0_23])).

fof(c_0_35,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
      | ~ m1_subset_1(X14,u1_struct_0(X12))
      | ~ v3_pre_topc(X13,X12)
      | ~ r2_hidden(X14,X13)
      | m1_connsp_2(X13,X12,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,esk9_0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( m1_connsp_2(esk8_0,esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_31,c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk2_0,X1,esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_19]),c_0_22])]),c_0_25]),c_0_23])).

cnf(c_0_39,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_24])).

cnf(c_0_41,plain,
    ( v3_pre_topc(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_tsep_1(X1,X2,X3))
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_24])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_22])])).

cnf(c_0_46,plain,
    ( v3_pre_topc(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,esk1_8(X2,X3,X4,X1,X5,X6,X7,X8))
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_48,negated_conjecture,
    ( m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0))
    | ~ v3_pre_topc(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])])).

cnf(c_0_49,negated_conjecture,
    ( v3_pre_topc(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,esk1_8(X2,X3,X4,X1,X1,X1,X5,X6))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X6,X4,X1)
    | ~ m1_connsp_2(X5,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_51,negated_conjecture,
    ( m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),X1)
    | v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_30]),c_0_37])])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk5_0,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_53,plain,
    ( r1_tarski(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k2_xboole_0(X7,X8))
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
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,negated_conjecture,
    ( ~ m1_connsp_2(X1,k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)
    | ~ r1_tarski(X1,k2_xboole_0(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_55,negated_conjecture,
    ( m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)
    | v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_16]),c_0_30]),c_0_37])])).

cnf(c_0_56,plain,
    ( r1_tarski(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k2_xboole_0(X5,X6))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X6,X3,X4)
    | ~ m1_connsp_2(X5,X2,X4)
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))
    | ~ r1_tarski(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k2_xboole_0(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k2_xboole_0(X1,X2))
    | ~ m1_connsp_2(X2,esk4_0,esk5_0)
    | ~ m1_connsp_2(X1,esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_59,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,negated_conjecture,
    ( v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_30]),c_0_37])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_20]),c_0_21]),c_0_22])]),c_0_25]),c_0_24]),c_0_23]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:38:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.46/0.66  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S059A
% 0.46/0.66  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.46/0.66  #
% 0.46/0.66  # Preprocessing time       : 0.028 s
% 0.46/0.66  # Presaturation interreduction done
% 0.46/0.66  
% 0.46/0.66  # Proof found!
% 0.46/0.66  # SZS status Theorem
% 0.46/0.66  # SZS output start CNFRefutation
% 0.46/0.66  fof(t21_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((X5=X4&X6=X4)=>![X7]:(m1_connsp_2(X7,X2,X5)=>![X8]:(m1_connsp_2(X8,X3,X6)=>?[X9]:(m1_connsp_2(X9,k1_tsep_1(X1,X2,X3),X4)&r1_tarski(X9,k2_xboole_0(X7,X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tmap_1)).
% 0.46/0.66  fof(t20_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((X5=X4&X6=X4)=>![X7]:(m1_connsp_2(X7,X2,X5)=>![X8]:(m1_connsp_2(X8,X3,X6)=>?[X9]:(((m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))&v3_pre_topc(X9,k1_tsep_1(X1,X2,X3)))&r2_hidden(X4,X9))&r1_tarski(X9,k2_xboole_0(X7,X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tmap_1)).
% 0.46/0.66  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.46/0.66  fof(fc1_tmap_1, axiom, ![X1, X2, X3]:(((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&v2_pre_topc(k1_tsep_1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tmap_1)).
% 0.46/0.66  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.46/0.66  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.46/0.66  fof(c_0_6, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X3))=>((X5=X4&X6=X4)=>![X7]:(m1_connsp_2(X7,X2,X5)=>![X8]:(m1_connsp_2(X8,X3,X6)=>?[X9]:(m1_connsp_2(X9,k1_tsep_1(X1,X2,X3),X4)&r1_tarski(X9,k2_xboole_0(X7,X8))))))))))))), inference(assume_negation,[status(cth)],[t21_tmap_1])).
% 0.46/0.66  fof(c_0_7, plain, ![X21, X22, X23, X24, X25, X26, X27, X28]:((((m1_subset_1(esk1_8(X21,X22,X23,X24,X25,X26,X27,X28),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X22,X23))))|~m1_connsp_2(X28,X23,X26)|~m1_connsp_2(X27,X22,X25)|(X25!=X24|X26!=X24)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v3_pre_topc(esk1_8(X21,X22,X23,X24,X25,X26,X27,X28),k1_tsep_1(X21,X22,X23))|~m1_connsp_2(X28,X23,X26)|~m1_connsp_2(X27,X22,X25)|(X25!=X24|X26!=X24)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r2_hidden(X24,esk1_8(X21,X22,X23,X24,X25,X26,X27,X28))|~m1_connsp_2(X28,X23,X26)|~m1_connsp_2(X27,X22,X25)|(X25!=X24|X26!=X24)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))))&(r1_tarski(esk1_8(X21,X22,X23,X24,X25,X26,X27,X28),k2_xboole_0(X27,X28))|~m1_connsp_2(X28,X23,X26)|~m1_connsp_2(X27,X22,X25)|(X25!=X24|X26!=X24)|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(X22))|~m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))|(v2_struct_0(X23)|~m1_pre_topc(X23,X21))|(v2_struct_0(X22)|~m1_pre_topc(X22,X21))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t20_tmap_1])])])])])])).
% 0.46/0.66  fof(c_0_8, negated_conjecture, ![X38]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&((esk6_0=esk5_0&esk7_0=esk5_0)&(m1_connsp_2(esk8_0,esk3_0,esk6_0)&(m1_connsp_2(esk9_0,esk4_0,esk7_0)&(~m1_connsp_2(X38,k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(X38,k2_xboole_0(esk8_0,esk9_0)))))))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])])).
% 0.46/0.66  cnf(c_0_9, plain, (m1_subset_1(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X8,X3,X6)|~m1_connsp_2(X7,X2,X5)|X5!=X4|X6!=X4|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_11, negated_conjecture, (esk7_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_13, negated_conjecture, (esk6_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  fof(c_0_14, plain, ![X15, X16, X17]:(((~v2_struct_0(k1_tsep_1(X15,X16,X17))|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15)))&(v1_pre_topc(k1_tsep_1(X15,X16,X17))|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15))))&(m1_pre_topc(k1_tsep_1(X15,X16,X17),X15)|(v2_struct_0(X15)|~l1_pre_topc(X15)|v2_struct_0(X16)|~m1_pre_topc(X16,X15)|v2_struct_0(X17)|~m1_pre_topc(X17,X15)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.46/0.66  cnf(c_0_15, plain, (m1_subset_1(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X6,X3,X4)|~m1_connsp_2(X5,X2,X4)|~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_9])])).
% 0.46/0.66  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.46/0.66  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk3_0))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.46/0.66  cnf(c_0_19, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_26, negated_conjecture, (m1_connsp_2(esk9_0,esk4_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  fof(c_0_27, plain, ![X18, X19, X20]:(((~v2_struct_0(k1_tsep_1(X18,X19,X20))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|v2_struct_0(X19)|~m1_pre_topc(X19,X18)|v2_struct_0(X20)|~m1_pre_topc(X20,X18)))&(v1_pre_topc(k1_tsep_1(X18,X19,X20))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|v2_struct_0(X19)|~m1_pre_topc(X19,X18)|v2_struct_0(X20)|~m1_pre_topc(X20,X18))))&(v2_pre_topc(k1_tsep_1(X18,X19,X20))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|v2_struct_0(X19)|~m1_pre_topc(X19,X18)|v2_struct_0(X20)|~m1_pre_topc(X20,X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_tmap_1])])])])).
% 0.46/0.66  cnf(c_0_28, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.66  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))|~m1_connsp_2(X2,esk4_0,esk5_0)|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24]), c_0_25])).
% 0.46/0.66  cnf(c_0_30, negated_conjecture, (m1_connsp_2(esk9_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_26, c_0_11])).
% 0.46/0.66  cnf(c_0_31, negated_conjecture, (m1_connsp_2(esk8_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_32, plain, (v2_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.46/0.66  fof(c_0_33, plain, ![X10, X11]:(~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|l1_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.46/0.66  cnf(c_0_34, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk2_0,X1,esk4_0),esk2_0)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_20]), c_0_22])]), c_0_25]), c_0_23])).
% 0.46/0.66  fof(c_0_35, plain, ![X12, X13, X14]:(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(~m1_subset_1(X14,u1_struct_0(X12))|(~v3_pre_topc(X13,X12)|~r2_hidden(X14,X13)|m1_connsp_2(X13,X12,X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.46/0.66  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,esk9_0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.46/0.66  cnf(c_0_37, negated_conjecture, (m1_connsp_2(esk8_0,esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_31, c_0_13])).
% 0.46/0.66  cnf(c_0_38, negated_conjecture, (v2_pre_topc(k1_tsep_1(esk2_0,X1,esk4_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_19]), c_0_22])]), c_0_25]), c_0_23])).
% 0.46/0.66  cnf(c_0_39, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.46/0.66  cnf(c_0_40, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0),esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_24])).
% 0.46/0.66  cnf(c_0_41, plain, (v3_pre_topc(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k1_tsep_1(X1,X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X8,X3,X6)|~m1_connsp_2(X7,X2,X5)|X5!=X4|X6!=X4|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_42, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.46/0.66  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.46/0.66  cnf(c_0_44, negated_conjecture, (v2_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_24])).
% 0.46/0.66  cnf(c_0_45, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_22])])).
% 0.46/0.66  cnf(c_0_46, plain, (v3_pre_topc(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k1_tsep_1(X1,X2,X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X6,X3,X4)|~m1_connsp_2(X5,X2,X4)|~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_41])])).
% 0.46/0.66  cnf(c_0_47, plain, (r2_hidden(X1,esk1_8(X2,X3,X4,X1,X5,X6,X7,X8))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_connsp_2(X8,X4,X6)|~m1_connsp_2(X7,X3,X5)|X5!=X1|X6!=X1|~m1_subset_1(X6,u1_struct_0(X4))|~m1_subset_1(X5,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_48, negated_conjecture, (m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),X1)|v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~r2_hidden(X1,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0))|~v3_pre_topc(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])])).
% 0.46/0.66  cnf(c_0_49, negated_conjecture, (v3_pre_topc(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k1_tsep_1(esk2_0,esk3_0,esk4_0))|~m1_connsp_2(X2,esk4_0,esk5_0)|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24]), c_0_25])).
% 0.46/0.66  cnf(c_0_50, plain, (r2_hidden(X1,esk1_8(X2,X3,X4,X1,X1,X1,X5,X6))|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_connsp_2(X6,X4,X1)|~m1_connsp_2(X5,X3,X1)|~m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))|~m1_subset_1(X1,u1_struct_0(X4))|~m1_subset_1(X1,u1_struct_0(X3))|~v2_pre_topc(X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.46/0.66  cnf(c_0_51, negated_conjecture, (m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),X1)|v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~r2_hidden(X1,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0))|~m1_subset_1(X1,u1_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_30]), c_0_37])])).
% 0.46/0.66  cnf(c_0_52, negated_conjecture, (r2_hidden(esk5_0,esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2))|~m1_connsp_2(X2,esk4_0,esk5_0)|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24]), c_0_25])).
% 0.46/0.66  cnf(c_0_53, plain, (r1_tarski(esk1_8(X1,X2,X3,X4,X5,X6,X7,X8),k2_xboole_0(X7,X8))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X8,X3,X6)|~m1_connsp_2(X7,X2,X5)|X5!=X4|X6!=X4|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.46/0.66  cnf(c_0_54, negated_conjecture, (~m1_connsp_2(X1,k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)|~r1_tarski(X1,k2_xboole_0(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.46/0.66  cnf(c_0_55, negated_conjecture, (m1_connsp_2(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k1_tsep_1(esk2_0,esk3_0,esk4_0),esk5_0)|v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_16]), c_0_30]), c_0_37])])).
% 0.46/0.66  cnf(c_0_56, plain, (r1_tarski(esk1_8(X1,X2,X3,X4,X4,X4,X5,X6),k2_xboole_0(X5,X6))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X6,X3,X4)|~m1_connsp_2(X5,X2,X4)|~m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X4,u1_struct_0(X3))|~m1_subset_1(X4,u1_struct_0(X2))|~v2_pre_topc(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 0.46/0.66  cnf(c_0_57, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))|~r1_tarski(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,esk8_0,esk9_0),k2_xboole_0(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.46/0.66  cnf(c_0_58, negated_conjecture, (r1_tarski(esk1_8(esk2_0,esk3_0,esk4_0,esk5_0,esk5_0,esk5_0,X1,X2),k2_xboole_0(X1,X2))|~m1_connsp_2(X2,esk4_0,esk5_0)|~m1_connsp_2(X1,esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24]), c_0_25])).
% 0.46/0.66  cnf(c_0_59, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.46/0.66  cnf(c_0_60, negated_conjecture, (v2_struct_0(k1_tsep_1(esk2_0,esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_30]), c_0_37])])).
% 0.46/0.66  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_20]), c_0_21]), c_0_22])]), c_0_25]), c_0_24]), c_0_23]), ['proof']).
% 0.46/0.66  # SZS output end CNFRefutation
% 0.46/0.66  # Proof object total steps             : 62
% 0.46/0.66  # Proof object clause steps            : 49
% 0.46/0.66  # Proof object formula steps           : 13
% 0.46/0.66  # Proof object conjectures             : 39
% 0.46/0.66  # Proof object clause conjectures      : 36
% 0.46/0.66  # Proof object formula conjectures     : 3
% 0.46/0.66  # Proof object initial clauses used    : 24
% 0.46/0.66  # Proof object initial formulas used   : 6
% 0.46/0.66  # Proof object generating inferences   : 17
% 0.46/0.66  # Proof object simplifying inferences  : 85
% 0.46/0.66  # Training examples: 0 positive, 0 negative
% 0.46/0.66  # Parsed axioms                        : 6
% 0.46/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.46/0.66  # Initial clauses                      : 27
% 0.46/0.66  # Removed in clause preprocessing      : 0
% 0.46/0.66  # Initial clauses in saturation        : 27
% 0.46/0.66  # Processed clauses                    : 859
% 0.46/0.66  # ...of these trivial                  : 0
% 0.46/0.66  # ...subsumed                          : 2
% 0.46/0.66  # ...remaining for further processing  : 857
% 0.46/0.66  # Other redundant clauses eliminated   : 8
% 0.46/0.66  # Clauses deleted for lack of memory   : 0
% 0.46/0.66  # Backward-subsumed                    : 1
% 0.46/0.66  # Backward-rewritten                   : 230
% 0.46/0.66  # Generated clauses                    : 15916
% 0.46/0.66  # ...of the previous two non-trivial   : 15915
% 0.46/0.66  # Contextual simplify-reflections      : 0
% 0.46/0.66  # Paramodulations                      : 15912
% 0.46/0.66  # Factorizations                       : 0
% 0.46/0.66  # Equation resolutions                 : 8
% 0.46/0.66  # Propositional unsat checks           : 0
% 0.46/0.66  #    Propositional check models        : 0
% 0.46/0.66  #    Propositional check unsatisfiable : 0
% 0.46/0.66  #    Propositional clauses             : 0
% 0.46/0.66  #    Propositional clauses after purity: 0
% 0.46/0.66  #    Propositional unsat core size     : 0
% 0.46/0.66  #    Propositional preprocessing time  : 0.000
% 0.46/0.66  #    Propositional encoding time       : 0.000
% 0.46/0.66  #    Propositional solver time         : 0.000
% 0.46/0.66  #    Success case prop preproc time    : 0.000
% 0.46/0.66  #    Success case prop encoding time   : 0.000
% 0.46/0.66  #    Success case prop solver time     : 0.000
% 0.46/0.66  # Current number of processed clauses  : 597
% 0.46/0.66  #    Positive orientable unit clauses  : 31
% 0.46/0.66  #    Positive unorientable unit clauses: 0
% 0.46/0.66  #    Negative unit clauses             : 3
% 0.46/0.66  #    Non-unit-clauses                  : 563
% 0.46/0.66  # Current number of unprocessed clauses: 15108
% 0.46/0.66  # ...number of literals in the above   : 83600
% 0.46/0.66  # Current number of archived formulas  : 0
% 0.46/0.66  # Current number of archived clauses   : 256
% 0.46/0.66  # Clause-clause subsumption calls (NU) : 287394
% 0.46/0.66  # Rec. Clause-clause subsumption calls : 45496
% 0.46/0.66  # Non-unit clause-clause subsumptions  : 3
% 0.46/0.66  # Unit Clause-clause subsumption calls : 550
% 0.46/0.66  # Rewrite failures with RHS unbound    : 0
% 0.46/0.66  # BW rewrite match attempts            : 16
% 0.46/0.66  # BW rewrite match successes           : 1
% 0.46/0.66  # Condensation attempts                : 0
% 0.46/0.66  # Condensation successes               : 0
% 0.46/0.66  # Termbank termtop insertions          : 822212
% 0.46/0.66  
% 0.46/0.66  # -------------------------------------------------
% 0.46/0.66  # User time                : 0.306 s
% 0.46/0.66  # System time              : 0.015 s
% 0.46/0.66  # Total time               : 0.321 s
% 0.46/0.66  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
