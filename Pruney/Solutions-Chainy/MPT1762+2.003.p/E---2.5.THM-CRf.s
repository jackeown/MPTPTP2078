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
% DateTime   : Thu Dec  3 11:17:35 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 468 expanded)
%              Number of clauses        :   64 ( 165 expanded)
%              Number of leaves         :   11 ( 114 expanded)
%              Depth                    :   23
%              Number of atoms          :  431 (5535 expanded)
%              Number of equality atoms :   45 ( 279 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_tmap_1,conjecture,(
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
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ( ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( r2_hidden(X7,u1_struct_0(X3))
                                   => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                             => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t173_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

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
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => ( ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( r2_hidden(X7,u1_struct_0(X3))
                                     => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                               => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_tmap_1])).

fof(c_0_12,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | l1_pre_topc(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_13,negated_conjecture,(
    ! [X41] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk2_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk2_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
      & m1_pre_topc(esk4_0,esk5_0)
      & v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X41,u1_struct_0(esk5_0))
        | ~ r2_hidden(X41,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X41) = k1_funct_1(esk7_0,X41) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).

fof(c_0_14,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_15,plain,(
    ! [X32,X33,X34] :
      ( ( ~ r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | m1_pre_topc(X33,X34)
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_pre_topc(X33,X34)
        | r1_tarski(u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_pre_topc(X34,X32)
        | ~ m1_pre_topc(X33,X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

fof(c_0_16,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | m1_pre_topc(X31,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_17,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X20,X21] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | v2_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_25,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( ( m1_subset_1(esk1_5(X14,X15,X16,X17,X18),X14)
        | k2_partfun1(X14,X15,X16,X17) = X18
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X15)))
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X14))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( r2_hidden(esk1_5(X14,X15,X16,X17,X18),X17)
        | k2_partfun1(X14,X15,X16,X17) = X18
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X15)))
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X14))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) )
      & ( k3_funct_2(X14,X15,X16,esk1_5(X14,X15,X16,X17,X18)) != k1_funct_1(X18,esk1_5(X14,X15,X16,X17,X18))
        | k2_partfun1(X14,X15,X16,X17) = X18
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X17,X15)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X15)))
        | v1_xboole_0(X17)
        | ~ m1_subset_1(X17,k1_zfmisc_1(X14))
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X14,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
        | v1_xboole_0(X15)
        | v1_xboole_0(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

cnf(c_0_28,plain,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_18]),c_0_19]),c_0_26])])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_pre_topc(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_24]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_37,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_38,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | m1_subset_1(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),X1)
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_46,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_47,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_24])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_49]),c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_51]),c_0_19])])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),X4)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_48]),c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_57,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X3,esk1_5(X1,X2,X3,X4,X5)) != k1_funct_1(X5,esk1_5(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0)) = esk7_0
    | r2_hidden(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_55]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,u1_struct_0(esk3_0),X2,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0)) != k1_funct_1(esk7_0,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_62,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_63,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | r2_hidden(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_64,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_48]),c_0_60])])).

cnf(c_0_65,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0)) != k1_funct_1(esk7_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_66,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_65])).

fof(c_0_67,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X26)
      | ~ m1_pre_topc(X29,X26)
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X27))
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))
      | ~ m1_pre_topc(X29,X28)
      | k3_tmap_1(X26,X27,X28,X29,X30) = k2_partfun1(u1_struct_0(X28),u1_struct_0(X27),X30,u1_struct_0(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

cnf(c_0_68,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_66]),c_0_45])).

cnf(c_0_69,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_71,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_48]),c_0_24])])).

cnf(c_0_72,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_39]),c_0_60]),c_0_70]),c_0_40]),c_0_41])]),c_0_56])).

cnf(c_0_73,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_71]),c_0_50])).

cnf(c_0_74,negated_conjecture,
    ( k3_tmap_1(X1,esk3_0,esk5_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_36])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_76,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_48]),c_0_53])])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_78,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0) = k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_18]),c_0_51]),c_0_19]),c_0_26])]),c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_76]),c_0_56])).

fof(c_0_80,plain,(
    ! [X10,X11,X12,X13] :
      ( ( ~ r2_funct_2(X10,X11,X12,X13)
        | X12 = X13
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X10,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) )
      & ( X12 != X13
        | r2_funct_2(X10,X11,X12,X13)
        | ~ v1_funct_1(X12)
        | ~ v1_funct_2(X12,X10,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X10,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_81,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)),esk7_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_48]),c_0_60])])).

cnf(c_0_83,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk7_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_33]),c_0_34]),c_0_32])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.029 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t73_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(r2_hidden(X7,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7)=k1_funct_1(X6,X7)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_tmap_1)).
% 0.13/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.38  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.13/0.38  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.13/0.38  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.13/0.38  fof(t173_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(![X6]:(m1_subset_1(X6,X1)=>(r2_hidden(X6,X4)=>k3_funct_2(X1,X2,X3,X6)=k1_funct_1(X5,X6)))=>k2_partfun1(X1,X2,X3,X4)=X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 0.13/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.38  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.13/0.38  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(r2_hidden(X7,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7)=k1_funct_1(X6,X7)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6)))))))))), inference(assume_negation,[status(cth)],[t73_tmap_1])).
% 0.13/0.38  fof(c_0_12, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|l1_pre_topc(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.38  fof(c_0_13, negated_conjecture, ![X41]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(m1_pre_topc(esk4_0,esk5_0)&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X41,u1_struct_0(esk5_0))|(~r2_hidden(X41,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X41)=k1_funct_1(esk7_0,X41)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0))))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.38  fof(c_0_15, plain, ![X32, X33, X34]:((~r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|m1_pre_topc(X33,X34)|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~m1_pre_topc(X33,X34)|r1_tarski(u1_struct_0(X33),u1_struct_0(X34))|~m1_pre_topc(X34,X32)|~m1_pre_topc(X33,X32)|(~v2_pre_topc(X32)|~l1_pre_topc(X32)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.13/0.38  fof(c_0_16, plain, ![X31]:(~l1_pre_topc(X31)|m1_pre_topc(X31,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.13/0.38  cnf(c_0_17, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_20, plain, ![X20, X21]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|v2_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.13/0.38  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_22, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_23, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.13/0.38  cnf(c_0_25, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_27, plain, ![X14, X15, X16, X17, X18]:((m1_subset_1(esk1_5(X14,X15,X16,X17,X18),X14)|k2_partfun1(X14,X15,X16,X17)=X18|(~v1_funct_1(X18)|~v1_funct_2(X18,X17,X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X15))))|(v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(X14)))|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))|v1_xboole_0(X15)|v1_xboole_0(X14))&((r2_hidden(esk1_5(X14,X15,X16,X17,X18),X17)|k2_partfun1(X14,X15,X16,X17)=X18|(~v1_funct_1(X18)|~v1_funct_2(X18,X17,X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X15))))|(v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(X14)))|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))|v1_xboole_0(X15)|v1_xboole_0(X14))&(k3_funct_2(X14,X15,X16,esk1_5(X14,X15,X16,X17,X18))!=k1_funct_1(X18,esk1_5(X14,X15,X16,X17,X18))|k2_partfun1(X14,X15,X16,X17)=X18|(~v1_funct_1(X18)|~v1_funct_2(X18,X17,X15)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X17,X15))))|(v1_xboole_0(X17)|~m1_subset_1(X17,k1_zfmisc_1(X14)))|(~v1_funct_1(X16)|~v1_funct_2(X16,X14,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))|v1_xboole_0(X15)|v1_xboole_0(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).
% 0.13/0.38  cnf(c_0_28, plain, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X3)|~v2_pre_topc(X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk5_0,esk5_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.38  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_18]), c_0_19]), c_0_26])])).
% 0.13/0.38  cnf(c_0_31, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_35, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_pre_topc(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_24]), c_0_30])])).
% 0.13/0.38  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_37, plain, ![X25]:(v2_struct_0(X25)|~l1_struct_0(X25)|~v1_xboole_0(u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.38  cnf(c_0_38, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X1)|m1_subset_1(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),X1)|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_40, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_41, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_42, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_43, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_44, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_46, plain, ![X22]:(~l1_pre_topc(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.38  cnf(c_0_47, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.13/0.38  cnf(c_0_48, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.38  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_24])])).
% 0.13/0.38  cnf(c_0_50, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_52, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_49]), c_0_50])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_51]), c_0_19])])).
% 0.13/0.38  cnf(c_0_54, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),X4)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_55, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_48]), c_0_53])])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_57, plain, (k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|k3_funct_2(X1,X2,X3,esk1_5(X1,X2,X3,X4,X5))!=k1_funct_1(X5,esk1_5(X1,X2,X3,X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0))=esk7_0|r2_hidden(esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X1)|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_55]), c_0_56])).
% 0.13/0.38  cnf(c_0_60, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(X1)|k3_funct_2(X1,u1_struct_0(esk3_0),X2,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0))!=k1_funct_1(esk7_0,esk1_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk4_0),esk7_0))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_32]), c_0_33]), c_0_34])])).
% 0.13/0.38  cnf(c_0_62, negated_conjecture, (k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_63, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|r2_hidden(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.13/0.38  cnf(c_0_64, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|m1_subset_1(esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_48]), c_0_60])])).
% 0.13/0.38  cnf(c_0_65, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|k3_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0))!=k1_funct_1(esk7_0,esk1_5(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0),esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.13/0.38  cnf(c_0_66, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_65])).
% 0.13/0.38  fof(c_0_67, plain, ![X26, X27, X28, X29, X30]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_pre_topc(X28,X26)|(~m1_pre_topc(X29,X26)|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X27))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X27))))|(~m1_pre_topc(X29,X28)|k3_tmap_1(X26,X27,X28,X29,X30)=k2_partfun1(u1_struct_0(X28),u1_struct_0(X27),X30,u1_struct_0(X29)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.13/0.38  cnf(c_0_68, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_66]), c_0_45])).
% 0.13/0.38  cnf(c_0_69, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.13/0.38  cnf(c_0_70, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_71, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_48]), c_0_24])])).
% 0.13/0.38  cnf(c_0_72, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,X2,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk5_0)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_39]), c_0_60]), c_0_70]), c_0_40]), c_0_41])]), c_0_56])).
% 0.13/0.38  cnf(c_0_73, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_71]), c_0_50])).
% 0.13/0.38  cnf(c_0_74, negated_conjecture, (k3_tmap_1(X1,esk3_0,esk5_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_72, c_0_36])).
% 0.13/0.38  cnf(c_0_75, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_76, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_48]), c_0_53])])).
% 0.13/0.38  cnf(c_0_77, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_78, negated_conjecture, (k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0)=k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_18]), c_0_51]), c_0_19]), c_0_26])]), c_0_75])).
% 0.13/0.38  cnf(c_0_79, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_76]), c_0_56])).
% 0.13/0.38  fof(c_0_80, plain, ![X10, X11, X12, X13]:((~r2_funct_2(X10,X11,X12,X13)|X12=X13|(~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~v1_funct_1(X13)|~v1_funct_2(X13,X10,X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))&(X12!=X13|r2_funct_2(X10,X11,X12,X13)|(~v1_funct_1(X12)|~v1_funct_2(X12,X10,X11)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|~v1_funct_1(X13)|~v1_funct_2(X13,X10,X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.13/0.38  cnf(c_0_81, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0)),esk7_0)), inference(rw,[status(thm)],[c_0_77, c_0_78])).
% 0.13/0.38  cnf(c_0_82, negated_conjecture, (k2_partfun1(u1_struct_0(esk5_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk4_0))=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_48]), c_0_60])])).
% 0.13/0.38  cnf(c_0_83, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.13/0.38  cnf(c_0_84, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk7_0,esk7_0)), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.13/0.38  cnf(c_0_85, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_83])).
% 0.13/0.38  cnf(c_0_86, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_33]), c_0_34]), c_0_32])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 87
% 0.13/0.38  # Proof object clause steps            : 64
% 0.13/0.38  # Proof object formula steps           : 23
% 0.13/0.38  # Proof object conjectures             : 53
% 0.13/0.38  # Proof object clause conjectures      : 50
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 31
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 30
% 0.13/0.38  # Proof object simplifying inferences  : 69
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 34
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 34
% 0.13/0.38  # Processed clauses                    : 151
% 0.13/0.38  # ...of these trivial                  : 2
% 0.13/0.38  # ...subsumed                          : 3
% 0.13/0.38  # ...remaining for further processing  : 146
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 20
% 0.13/0.38  # Backward-rewritten                   : 8
% 0.13/0.38  # Generated clauses                    : 99
% 0.13/0.38  # ...of the previous two non-trivial   : 86
% 0.13/0.38  # Contextual simplify-reflections      : 2
% 0.13/0.38  # Paramodulations                      : 98
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
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
% 0.13/0.38  # Current number of processed clauses  : 83
% 0.13/0.38  #    Positive orientable unit clauses  : 34
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 5
% 0.13/0.38  #    Non-unit-clauses                  : 44
% 0.13/0.38  # Current number of unprocessed clauses: 3
% 0.13/0.38  # ...number of literals in the above   : 8
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 62
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 1356
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 89
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 25
% 0.13/0.38  # Unit Clause-clause subsumption calls : 98
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 16
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 6884
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.037 s
% 0.13/0.38  # System time              : 0.007 s
% 0.13/0.38  # Total time               : 0.043 s
% 0.13/0.38  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
