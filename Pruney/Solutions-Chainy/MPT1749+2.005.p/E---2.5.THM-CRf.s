%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:15 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 (2619 expanded)
%              Number of clauses        :   56 ( 868 expanded)
%              Number of leaves         :    8 ( 644 expanded)
%              Depth                    :   27
%              Number of atoms          :  379 (29076 expanded)
%              Number of equality atoms :   57 (1820 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tmap_1,conjecture,(
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
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d9_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( r2_funct_2(X1,X2,X3,X4)
          <=> ! [X5] :
                ( m1_subset_1(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_2)).

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
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                       => ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( r2_hidden(X6,u1_struct_0(X3))
                               => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_tmap_1])).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X26] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ v1_funct_1(X25)
      | ~ v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))
      | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))
      | ~ m1_pre_topc(X26,X23)
      | k2_tmap_1(X23,X24,X25,X26) = k2_partfun1(u1_struct_0(X23),u1_struct_0(X24),X25,u1_struct_0(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_10,negated_conjecture,(
    ! [X34] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & v2_pre_topc(esk4_0)
      & l1_pre_topc(esk4_0)
      & ~ v2_struct_0(esk5_0)
      & m1_pre_topc(esk5_0,esk4_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
      & v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
      & ( ~ m1_subset_1(X34,u1_struct_0(esk4_0))
        | ~ r2_hidden(X34,u1_struct_0(esk5_0))
        | k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X34) = k1_funct_1(esk7_0,X34) )
      & ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( m1_subset_1(esk2_5(X13,X14,X15,X16,X17),X13)
        | k2_partfun1(X13,X14,X15,X16) = X17
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X16,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X14)))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v1_xboole_0(X14)
        | v1_xboole_0(X13) )
      & ( r2_hidden(esk2_5(X13,X14,X15,X16,X17),X16)
        | k2_partfun1(X13,X14,X15,X16) = X17
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X16,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X14)))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v1_xboole_0(X14)
        | v1_xboole_0(X13) )
      & ( k3_funct_2(X13,X14,X15,esk2_5(X13,X14,X15,X16,X17)) != k1_funct_1(X17,esk2_5(X13,X14,X15,X16,X17))
        | k2_partfun1(X13,X14,X15,X16) = X17
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X16,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X14)))
        | v1_xboole_0(X16)
        | ~ m1_subset_1(X16,k1_zfmisc_1(X13))
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v1_xboole_0(X14)
        | v1_xboole_0(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

cnf(c_0_12,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_22,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X1)) = k2_tmap_1(esk4_0,esk3_0,esk6_0,X1)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18]),c_0_19])]),c_0_20]),c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_31,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X1)
    | m1_subset_1(esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_32,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0)) = k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_28]),c_0_17])])).

fof(c_0_34,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_13]),c_0_32]),c_0_33]),c_0_18]),c_0_19])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_38,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_39,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_41,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_44,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_43]),c_0_21])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_5(X1,X2,X3,X4,X5),X4)
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_46,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_41]),c_0_17])])).

cnf(c_0_47,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0)) = esk7_0
    | r2_hidden(esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_48,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_46]),c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1) = k1_funct_1(esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | r2_hidden(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_13]),c_0_32]),c_0_33]),c_0_18]),c_0_19])])).

cnf(c_0_51,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_41]),c_0_16])])).

cnf(c_0_52,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_53,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_52]),c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_41]),c_0_42])])).

cnf(c_0_55,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_54]),c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_41]),c_0_17])])).

cnf(c_0_57,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X3,esk2_5(X1,X2,X3,X4,X5)) != k1_funct_1(X5,esk2_5(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_58,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_56]),c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(X1)
    | k3_funct_2(X1,u1_struct_0(esk3_0),X2,esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0)) != k1_funct_1(esk7_0,esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_60,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0)) = k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))
    | k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_16])])).

cnf(c_0_61,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_13]),c_0_32]),c_0_33]),c_0_18]),c_0_19])]),c_0_60])).

cnf(c_0_62,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_61]),c_0_37])).

cnf(c_0_63,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_41]),c_0_42])])).

cnf(c_0_64,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_63]),c_0_21])).

fof(c_0_65,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | ~ m1_subset_1(X11,X7)
        | k1_funct_1(X9,X11) = k1_funct_1(X10,X11)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( m1_subset_1(esk1_4(X7,X8,X9,X10),X7)
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( k1_funct_1(X9,esk1_4(X7,X8,X9,X10)) != k1_funct_1(X10,esk1_4(X7,X8,X9,X10))
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).

cnf(c_0_66,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_41]),c_0_17])])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_68,plain,
    ( r2_funct_2(X2,X3,X1,X4)
    | k1_funct_1(X1,esk1_4(X2,X3,X1,X4)) != k1_funct_1(X4,esk1_4(X2,X3,X1,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_69,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_66]),c_0_20])).

cnf(c_0_70,negated_conjecture,
    ( k1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk1_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)) != k1_funct_1(esk7_0,esk1_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))
    | ~ m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_24]),c_0_25]),c_0_26])])).

cnf(c_0_71,negated_conjecture,
    ( k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0) = esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_41]),c_0_16])])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_71]),c_0_71]),c_0_71]),c_0_71]),c_0_24]),c_0_71]),c_0_25]),c_0_71]),c_0_26])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:43:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 0.19/0.38  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.029 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t59_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.19/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.38  fof(t173_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(![X6]:(m1_subset_1(X6,X1)=>(r2_hidden(X6,X4)=>k3_funct_2(X1,X2,X3,X6)=k1_funct_1(X5,X6)))=>k2_partfun1(X1,X2,X3,X4)=X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_2)).
% 0.19/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.38  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(d9_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>![X5]:(m1_subset_1(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_2)).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t59_tmap_1])).
% 0.19/0.38  fof(c_0_9, plain, ![X23, X24, X25, X26]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~v1_funct_1(X25)|~v1_funct_2(X25,u1_struct_0(X23),u1_struct_0(X24))|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X24))))|(~m1_pre_topc(X26,X23)|k2_tmap_1(X23,X24,X25,X26)=k2_partfun1(u1_struct_0(X23),u1_struct_0(X24),X25,u1_struct_0(X26)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.38  fof(c_0_10, negated_conjecture, ![X34]:(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&((~m1_subset_1(X34,u1_struct_0(esk4_0))|(~r2_hidden(X34,u1_struct_0(esk5_0))|k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X34)=k1_funct_1(esk7_0,X34)))&~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X13, X14, X15, X16, X17]:((m1_subset_1(esk2_5(X13,X14,X15,X16,X17),X13)|k2_partfun1(X13,X14,X15,X16)=X17|(~v1_funct_1(X17)|~v1_funct_2(X17,X16,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X14))))|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(X13)))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))|v1_xboole_0(X14)|v1_xboole_0(X13))&((r2_hidden(esk2_5(X13,X14,X15,X16,X17),X16)|k2_partfun1(X13,X14,X15,X16)=X17|(~v1_funct_1(X17)|~v1_funct_2(X17,X16,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X14))))|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(X13)))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))|v1_xboole_0(X14)|v1_xboole_0(X13))&(k3_funct_2(X13,X14,X15,esk2_5(X13,X14,X15,X16,X17))!=k1_funct_1(X17,esk2_5(X13,X14,X15,X16,X17))|k2_partfun1(X13,X14,X15,X16)=X17|(~v1_funct_1(X17)|~v1_funct_2(X17,X16,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X16,X14))))|(v1_xboole_0(X16)|~m1_subset_1(X16,k1_zfmisc_1(X13)))|(~v1_funct_1(X15)|~v1_funct_2(X15,X13,X14)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))|v1_xboole_0(X14)|v1_xboole_0(X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).
% 0.19/0.38  cnf(c_0_12, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_14, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_22, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,X27)|m1_subset_1(u1_struct_0(X28),k1_zfmisc_1(u1_struct_0(X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.38  cnf(c_0_23, plain, (m1_subset_1(esk2_5(X1,X2,X3,X4,X5),X1)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(X1))=k2_tmap_1(esk4_0,esk3_0,esk6_0,X1)|~m1_pre_topc(X1,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17]), c_0_18]), c_0_19])]), c_0_20]), c_0_21])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_29, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  fof(c_0_30, plain, ![X22]:(v2_struct_0(X22)|~l1_struct_0(X22)|~v1_xboole_0(u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X1)|m1_subset_1(esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.38  cnf(c_0_32, negated_conjecture, (k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0))=k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_28]), c_0_17])])).
% 0.19/0.38  fof(c_0_34, plain, ![X20, X21]:(~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|l1_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.38  cnf(c_0_35, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_13]), c_0_32]), c_0_33]), c_0_18]), c_0_19])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_38, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_39, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.38  cnf(c_0_41, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_28]), c_0_17])])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_43]), c_0_21])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(esk2_5(X1,X2,X3,X4,X5),X4)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_41]), c_0_17])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0))=esk7_0|r2_hidden(esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_46]), c_0_20])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,X1)=k1_funct_1(esk7_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|r2_hidden(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_13]), c_0_32]), c_0_33]), c_0_18]), c_0_19])])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|m1_subset_1(esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_41]), c_0_16])])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_52]), c_0_37])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_41]), c_0_42])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_54]), c_0_21])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_41]), c_0_17])])).
% 0.19/0.38  cnf(c_0_57, plain, (k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|k3_funct_2(X1,X2,X3,esk2_5(X1,X2,X3,X4,X5))!=k1_funct_1(X5,esk2_5(X1,X2,X3,X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_56]), c_0_20])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0))=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(X1)|k3_funct_2(X1,u1_struct_0(esk3_0),X2,esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0))!=k1_funct_1(esk7_0,esk2_5(X1,u1_struct_0(esk3_0),X2,u1_struct_0(esk5_0),esk7_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk3_0))|~v1_funct_1(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))=k1_funct_1(esk7_0,esk2_5(u1_struct_0(esk4_0),u1_struct_0(esk3_0),esk6_0,u1_struct_0(esk5_0),esk7_0))|k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_41]), c_0_16])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_13]), c_0_32]), c_0_33]), c_0_18]), c_0_19])]), c_0_60])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk4_0))|~l1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_61]), c_0_37])).
% 0.19/0.38  cnf(c_0_63, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_41]), c_0_42])])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))|~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_63]), c_0_21])).
% 0.19/0.38  fof(c_0_65, plain, ![X7, X8, X9, X10, X11]:((~r2_funct_2(X7,X8,X9,X10)|(~m1_subset_1(X11,X7)|k1_funct_1(X9,X11)=k1_funct_1(X10,X11))|(~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&((m1_subset_1(esk1_4(X7,X8,X9,X10),X7)|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(k1_funct_1(X9,esk1_4(X7,X8,X9,X10))!=k1_funct_1(X10,esk1_4(X7,X8,X9,X10))|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_funct_2])])])])])).
% 0.19/0.38  cnf(c_0_66, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_41]), c_0_17])])).
% 0.19/0.38  cnf(c_0_67, negated_conjecture, (~r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_68, plain, (r2_funct_2(X2,X3,X1,X4)|k1_funct_1(X1,esk1_4(X2,X3,X1,X4))!=k1_funct_1(X4,esk1_4(X2,X3,X1,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.38  cnf(c_0_69, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_66]), c_0_20])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (k1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk1_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))!=k1_funct_1(esk7_0,esk1_4(u1_struct_0(esk5_0),u1_struct_0(esk3_0),k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),esk7_0))|~m1_subset_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))|~v1_funct_2(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0),u1_struct_0(esk5_0),u1_struct_0(esk3_0))|~v1_funct_1(k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_24]), c_0_25]), c_0_26])])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, (k2_tmap_1(esk4_0,esk3_0,esk6_0,esk5_0)=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_41]), c_0_16])])).
% 0.19/0.38  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_71]), c_0_71]), c_0_71]), c_0_71]), c_0_24]), c_0_71]), c_0_25]), c_0_71]), c_0_26])]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 73
% 0.19/0.38  # Proof object clause steps            : 56
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 50
% 0.19/0.38  # Proof object clause conjectures      : 47
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 25
% 0.19/0.38  # Proof object initial formulas used   : 8
% 0.19/0.38  # Proof object generating inferences   : 30
% 0.19/0.38  # Proof object simplifying inferences  : 80
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 8
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 27
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 102
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 102
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 17
% 0.19/0.38  # Backward-rewritten                   : 7
% 0.19/0.38  # Generated clauses                    : 49
% 0.19/0.38  # ...of the previous two non-trivial   : 50
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 49
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 51
% 0.19/0.38  #    Positive orientable unit clauses  : 14
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 3
% 0.19/0.38  #    Non-unit-clauses                  : 34
% 0.19/0.38  # Current number of unprocessed clauses: 1
% 0.19/0.38  # ...number of literals in the above   : 6
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 51
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 488
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 42
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 19
% 0.19/0.38  # Unit Clause-clause subsumption calls : 14
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 3
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 5638
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.038 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.041 s
% 0.19/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
