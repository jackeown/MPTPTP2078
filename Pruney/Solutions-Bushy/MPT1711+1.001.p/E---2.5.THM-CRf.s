%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1711+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:38 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 (1679 expanded)
%              Number of clauses        :   69 ( 580 expanded)
%              Number of leaves         :    8 ( 403 expanded)
%              Depth                    :   11
%              Number of atoms          :  506 (19361 expanded)
%              Number of equality atoms :    8 (1810 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t20_tmap_1,conjecture,(
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

fof(t8_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v3_pre_topc(X4,X1)
                    & r1_tarski(X4,X3)
                    & r2_hidden(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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

fof(t19_tmap_1,axiom,(
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
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ! [X6] :
                          ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
                         => ~ ( v3_pre_topc(X5,X2)
                              & r2_hidden(X4,X5)
                              & v3_pre_topc(X6,X3)
                              & r2_hidden(X4,X6)
                              & ! [X7] :
                                  ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
                                 => ~ ( v3_pre_topc(X7,k1_tsep_1(X1,X2,X3))
                                      & r2_hidden(X4,X7)
                                      & r1_tarski(X7,k2_xboole_0(X5,X6)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tmap_1)).

fof(t13_xboole_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(c_0_8,negated_conjecture,(
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
                                          ( m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
                                          & v3_pre_topc(X9,k1_tsep_1(X1,X2,X3))
                                          & r2_hidden(X4,X9)
                                          & r1_tarski(X9,k2_xboole_0(X7,X8)) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t20_tmap_1])).

fof(c_0_9,plain,(
    ! [X31,X32,X33,X35] :
      ( ( m1_subset_1(esk2_3(X31,X32,X33),k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_connsp_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( v3_pre_topc(esk2_3(X31,X32,X33),X31)
        | ~ m1_connsp_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r1_tarski(esk2_3(X31,X32,X33),X33)
        | ~ m1_connsp_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( r2_hidden(X32,esk2_3(X31,X32,X33))
        | ~ m1_connsp_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ v3_pre_topc(X35,X31)
        | ~ r1_tarski(X35,X33)
        | ~ r2_hidden(X32,X35)
        | m1_connsp_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31)))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_connsp_2])])])])])])).

fof(c_0_10,plain,(
    ! [X12,X13,X14] :
      ( v2_struct_0(X12)
      | ~ v2_pre_topc(X12)
      | ~ l1_pre_topc(X12)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | ~ m1_connsp_2(X14,X12,X13)
      | m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_11,negated_conjecture,(
    ! [X44] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk3_0)
      & m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))
      & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
      & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
      & esk7_0 = esk6_0
      & esk8_0 = esk6_0
      & m1_connsp_2(esk9_0,esk4_0,esk7_0)
      & m1_connsp_2(esk10_0,esk5_0,esk8_0)
      & ( ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0))))
        | ~ v3_pre_topc(X44,k1_tsep_1(esk3_0,esk4_0,esk5_0))
        | ~ r2_hidden(esk6_0,X44)
        | ~ r1_tarski(X44,k2_xboole_0(esk9_0,esk10_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_12,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_13,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_14,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_connsp_2(esk10_0,esk5_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( esk8_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_25,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_26,plain,(
    ! [X21,X22,X23,X24,X25,X26] :
      ( ( m1_subset_1(esk1_6(X21,X22,X23,X24,X25,X26),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X21,X22,X23))))
        | ~ v3_pre_topc(X25,X22)
        | ~ r2_hidden(X24,X25)
        | ~ v3_pre_topc(X26,X23)
        | ~ r2_hidden(X24,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(esk1_6(X21,X22,X23,X24,X25,X26),k1_tsep_1(X21,X22,X23))
        | ~ v3_pre_topc(X25,X22)
        | ~ r2_hidden(X24,X25)
        | ~ v3_pre_topc(X26,X23)
        | ~ r2_hidden(X24,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r2_hidden(X24,esk1_6(X21,X22,X23,X24,X25,X26))
        | ~ v3_pre_topc(X25,X22)
        | ~ r2_hidden(X24,X25)
        | ~ v3_pre_topc(X26,X23)
        | ~ r2_hidden(X24,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( r1_tarski(esk1_6(X21,X22,X23,X24,X25,X26),k2_xboole_0(X25,X26))
        | ~ v3_pre_topc(X25,X22)
        | ~ r2_hidden(X24,X25)
        | ~ v3_pre_topc(X26,X23)
        | ~ r2_hidden(X24,X26)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X24,u1_struct_0(k1_tsep_1(X21,X22,X23)))
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X21)
        | v2_struct_0(X22)
        | ~ m1_pre_topc(X22,X21)
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t19_tmap_1])])])])])])).

cnf(c_0_27,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( m1_connsp_2(esk10_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_17])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21]),c_0_23])])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_24,c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_38,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_tarski(X19,X20)
      | r1_tarski(k2_xboole_0(X17,X19),k2_xboole_0(X18,X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t13_xboole_1])])).

cnf(c_0_39,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X3)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_25,c_0_15])).

cnf(c_0_40,plain,
    ( r1_tarski(esk1_6(X1,X2,X3,X4,X5,X6),k2_xboole_0(X5,X6))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(X4,X5)
    | ~ v3_pre_topc(X6,X3)
    | ~ r2_hidden(X4,X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk5_0,esk6_0,esk10_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk2_3(esk5_0,esk6_0,esk10_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_37]),c_0_21])])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_37]),c_0_21]),c_0_23])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_49,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),k2_xboole_0(X2,X4))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk2_3(esk5_0,esk6_0,esk10_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_6(X1,X2,esk5_0,X3,X4,esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(X4,esk2_3(esk5_0,esk6_0,esk10_0)))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X3,X4)
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X1,X2,esk5_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk2_3(esk4_0,esk6_0,esk9_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk2_3(esk4_0,esk6_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,esk2_3(X2,X1,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X3,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_48,c_0_15])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,esk1_6(X2,X3,X4,X1,X5,X6))
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X5,X3)
    | ~ r2_hidden(X1,X5)
    | ~ v3_pre_topc(X6,X4)
    | ~ r2_hidden(X1,X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_56,plain,
    ( v3_pre_topc(esk1_6(X1,X2,X3,X4,X5,X6),k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(X4,X5)
    | ~ v3_pre_topc(X6,X3)
    | ~ r2_hidden(X4,X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,plain,
    ( m1_subset_1(esk1_6(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,X3))))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(X4,X5)
    | ~ v3_pre_topc(X6,X3)
    | ~ r2_hidden(X4,X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_58,plain,(
    ! [X28,X29,X30] :
      ( ~ r1_tarski(X28,X29)
      | ~ r1_tarski(X29,X30)
      | r1_tarski(X28,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_xboole_0(X1,esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(X2,esk10_0))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_3(esk4_0,esk6_0,esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk1_6(X1,esk4_0,esk5_0,X2,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X2,esk2_3(esk4_0,esk6_0,esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])]),c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_3(esk5_0,esk6_0,esk10_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,esk2_3(esk4_0,esk6_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_43]),c_0_44]),c_0_45]),c_0_46])]),c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(X1,esk1_6(X2,X3,esk5_0,X1,X4,esk2_3(esk5_0,esk6_0,esk10_0)))
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(X1,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X1,X4)
    | ~ v3_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,X3,esk5_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_41]),c_0_42])]),c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(esk1_6(X1,X2,esk5_0,X3,X4,esk2_3(esk5_0,esk6_0,esk10_0)),k1_tsep_1(X1,X2,esk5_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X3,X4)
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X1,X2,esk5_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_41]),c_0_42])]),c_0_32])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk1_6(X1,X2,esk5_0,X3,X4,esk2_3(esk5_0,esk6_0,esk10_0)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X2,esk5_0))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X3,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X3,X4)
    | ~ v3_pre_topc(X4,X2)
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X1,X2,esk5_0)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_41]),c_0_42])]),c_0_32])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk1_6(X1,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_71,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(X1,esk1_6(X2,esk4_0,esk5_0,X1,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)))
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X1,esk2_3(esk4_0,esk6_0,esk9_0))
    | ~ m1_subset_1(X1,u1_struct_0(k1_tsep_1(X2,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_52]),c_0_53])]),c_0_47])).

cnf(c_0_73,negated_conjecture,
    ( v3_pre_topc(esk1_6(X1,esk4_0,esk5_0,X2,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k1_tsep_1(X1,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X2,esk2_3(esk4_0,esk6_0,esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_52]),c_0_53])]),c_0_47])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_6(X1,esk4_0,esk5_0,X2,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0))))
    | v2_struct_0(X1)
    | ~ r2_hidden(X2,esk2_3(esk5_0,esk6_0,esk10_0))
    | ~ r2_hidden(X2,esk2_3(esk4_0,esk6_0,esk9_0))
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_52]),c_0_53])]),c_0_47])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(X1,k2_xboole_0(esk9_0,esk10_0))
    | ~ r1_tarski(X1,k2_xboole_0(esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk1_6(esk3_0,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_20]),c_0_70]),c_0_37]),c_0_21]),c_0_23])]),c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk6_0,esk1_6(X1,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_62]),c_0_63])])).

cnf(c_0_78,negated_conjecture,
    ( v3_pre_topc(esk1_6(X1,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k1_tsep_1(X1,esk4_0,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_62]),c_0_63])])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk1_6(X1,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0))))
    | v2_struct_0(X1)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(X1,esk4_0,esk5_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_62]),c_0_63])])).

cnf(c_0_80,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0))))
    | ~ v3_pre_topc(X1,k1_tsep_1(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(esk6_0,X1)
    | ~ r1_tarski(X1,k2_xboole_0(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk1_6(esk3_0,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k2_xboole_0(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk6_0,esk1_6(esk3_0,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_20]),c_0_70]),c_0_37]),c_0_21]),c_0_23])]),c_0_71])).

cnf(c_0_83,negated_conjecture,
    ( v3_pre_topc(esk1_6(esk3_0,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k1_tsep_1(esk3_0,esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_20]),c_0_70]),c_0_37]),c_0_21]),c_0_23])]),c_0_71])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk1_6(esk3_0,esk4_0,esk5_0,esk6_0,esk2_3(esk4_0,esk6_0,esk9_0),esk2_3(esk5_0,esk6_0,esk10_0)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(esk3_0,esk4_0,esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_20]),c_0_70]),c_0_37]),c_0_21]),c_0_23])]),c_0_71])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_83]),c_0_84])]),
    [proof]).

%------------------------------------------------------------------------------
