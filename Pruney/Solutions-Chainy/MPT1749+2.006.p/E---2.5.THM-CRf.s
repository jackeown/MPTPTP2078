%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:15 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 362 expanded)
%              Number of clauses        :   42 ( 124 expanded)
%              Number of leaves         :    8 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  299 (3819 expanded)
%              Number of equality atoms :   31 ( 220 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_tmap_1)).

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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

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
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_10,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_11,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_12,negated_conjecture,(
    ! [X32] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X32,u1_struct_0(esk3_0))
        | ~ r2_hidden(X32,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X32) = k1_funct_1(esk6_0,X32) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( m1_subset_1(esk1_5(X11,X12,X13,X14,X15),X11)
        | k2_partfun1(X11,X12,X13,X14) = X15
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X14,X12)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X12)))
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X11))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | v1_xboole_0(X12)
        | v1_xboole_0(X11) )
      & ( r2_hidden(esk1_5(X11,X12,X13,X14,X15),X14)
        | k2_partfun1(X11,X12,X13,X14) = X15
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X14,X12)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X12)))
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X11))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | v1_xboole_0(X12)
        | v1_xboole_0(X11) )
      & ( k3_funct_2(X11,X12,X13,esk1_5(X11,X12,X13,X14,X15)) != k1_funct_1(X15,esk1_5(X11,X12,X13,X14,X15))
        | k2_partfun1(X11,X12,X13,X14) = X15
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,X14,X12)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X12)))
        | v1_xboole_0(X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(X11))
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | v1_xboole_0(X12)
        | v1_xboole_0(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_24,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_25,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_29,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_23])])).

cnf(c_0_31,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0)) = esk6_0
    | v1_xboole_0(X1)
    | k3_funct_2(X1,u1_struct_0(esk2_0),X2,esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0)) != k1_funct_1(esk6_0,esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_16]),c_0_17])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_20]),c_0_17])])).

cnf(c_0_41,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0)) = esk6_0
    | v1_xboole_0(X1)
    | m1_subset_1(esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0)) = esk6_0
    | r2_hidden(esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_27]),c_0_28])]),c_0_29]),c_0_30])).

fof(c_0_43,plain,(
    ! [X21,X22,X23,X24] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
      | ~ m1_pre_topc(X24,X21)
      | k2_tmap_1(X21,X22,X23,X24) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0
    | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0)) != k1_funct_1(esk6_0,esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0
    | m1_subset_1(esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0
    | r2_hidden(esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_52,plain,(
    ! [X7,X8,X9,X10] :
      ( ( ~ r2_funct_2(X7,X8,X9,X10)
        | X9 = X10
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( X9 != X10
        | r2_funct_2(X7,X8,X9,X10)
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,X7,X8)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X10)
        | ~ v1_funct_2(X10,X7,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_54,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_51]),c_0_16]),c_0_23]),c_0_17]),c_0_36]),c_0_38]),c_0_39])]),c_0_22]),c_0_32])).

cnf(c_0_55,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_26]),c_0_27]),c_0_28])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.13/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.040 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t59_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.13/0.39  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.13/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.13/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.13/0.39  fof(t173_funct_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:(~(v1_xboole_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:((~(v1_xboole_0(X4))&m1_subset_1(X4,k1_zfmisc_1(X1)))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X4,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))))=>(![X6]:(m1_subset_1(X6,X1)=>(r2_hidden(X6,X4)=>k3_funct_2(X1,X2,X3,X6)=k1_funct_1(X5,X6)))=>k2_partfun1(X1,X2,X3,X4)=X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_2)).
% 0.13/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.13/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.13/0.39  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.13/0.39  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t59_tmap_1])).
% 0.13/0.39  fof(c_0_9, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.13/0.39  fof(c_0_10, plain, ![X17]:(~l1_pre_topc(X17)|l1_struct_0(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.13/0.39  fof(c_0_11, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.13/0.39  fof(c_0_12, negated_conjecture, ![X32]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk3_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X32,u1_struct_0(esk3_0))|(~r2_hidden(X32,u1_struct_0(esk4_0))|k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X32)=k1_funct_1(esk6_0,X32)))&~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.13/0.39  cnf(c_0_13, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.39  cnf(c_0_14, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.39  cnf(c_0_15, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_16, negated_conjecture, (m1_pre_topc(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  fof(c_0_18, plain, ![X11, X12, X13, X14, X15]:((m1_subset_1(esk1_5(X11,X12,X13,X14,X15),X11)|k2_partfun1(X11,X12,X13,X14)=X15|(~v1_funct_1(X15)|~v1_funct_2(X15,X14,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X12))))|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))|v1_xboole_0(X12)|v1_xboole_0(X11))&((r2_hidden(esk1_5(X11,X12,X13,X14,X15),X14)|k2_partfun1(X11,X12,X13,X14)=X15|(~v1_funct_1(X15)|~v1_funct_2(X15,X14,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X12))))|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))|v1_xboole_0(X12)|v1_xboole_0(X11))&(k3_funct_2(X11,X12,X13,esk1_5(X11,X12,X13,X14,X15))!=k1_funct_1(X15,esk1_5(X11,X12,X13,X14,X15))|k2_partfun1(X11,X12,X13,X14)=X15|(~v1_funct_1(X15)|~v1_funct_2(X15,X14,X12)|~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X14,X12))))|(v1_xboole_0(X14)|~m1_subset_1(X14,k1_zfmisc_1(X11)))|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))|v1_xboole_0(X12)|v1_xboole_0(X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).
% 0.13/0.39  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_20, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  fof(c_0_24, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|m1_subset_1(u1_struct_0(X26),k1_zfmisc_1(u1_struct_0(X25))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.13/0.39  cnf(c_0_25, plain, (k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|k3_funct_2(X1,X2,X3,esk1_5(X1,X2,X3,X4,X5))!=k1_funct_1(X5,esk1_5(X1,X2,X3,X4,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_28, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_29, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_23])])).
% 0.13/0.39  cnf(c_0_31, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.39  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_33, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),X1)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_34, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),X4)|k2_partfun1(X1,X2,X3,X4)=X5|v1_xboole_0(X4)|v1_xboole_0(X2)|v1_xboole_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,X4,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X4,k1_zfmisc_1(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0))=esk6_0|v1_xboole_0(X1)|k3_funct_2(X1,u1_struct_0(esk2_0),X2,esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0))!=k1_funct_1(esk6_0,esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk2_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_16]), c_0_17])])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_40, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_20]), c_0_17])])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0))=esk6_0|v1_xboole_0(X1)|m1_subset_1(esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk2_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0))=esk6_0|r2_hidden(esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))|v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))|~m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))|~v1_funct_2(X2,X1,u1_struct_0(esk2_0))|~v1_funct_1(X2)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_26]), c_0_27]), c_0_28])]), c_0_29]), c_0_30])).
% 0.13/0.39  fof(c_0_43, plain, ![X21, X22, X23, X24]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_pre_topc(X24,X21)|k2_tmap_1(X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=esk6_0|k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0))!=k1_funct_1(esk6_0,esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1)=k1_funct_1(esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_46, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=esk6_0|m1_subset_1(esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=esk6_0|r2_hidden(esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.13/0.39  cnf(c_0_48, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=esk6_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  fof(c_0_52, plain, ![X7, X8, X9, X10]:((~r2_funct_2(X7,X8,X9,X10)|X9=X10|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(X9!=X10|r2_funct_2(X7,X8,X9,X10)|(~v1_funct_1(X9)|~v1_funct_2(X9,X7,X8)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X10)|~v1_funct_2(X10,X7,X8)|~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_54, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)=esk6_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_51]), c_0_16]), c_0_23]), c_0_17]), c_0_36]), c_0_38]), c_0_39])]), c_0_22]), c_0_32])).
% 0.13/0.39  cnf(c_0_55, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (~r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,esk6_0)), inference(rw,[status(thm)],[c_0_53, c_0_54])).
% 0.13/0.39  cnf(c_0_57, plain, (r2_funct_2(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_55])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_26]), c_0_27]), c_0_28])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 59
% 0.13/0.39  # Proof object clause steps            : 42
% 0.13/0.39  # Proof object formula steps           : 17
% 0.13/0.39  # Proof object conjectures             : 34
% 0.13/0.39  # Proof object clause conjectures      : 31
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 25
% 0.13/0.39  # Proof object initial formulas used   : 8
% 0.13/0.39  # Proof object generating inferences   : 15
% 0.13/0.39  # Proof object simplifying inferences  : 59
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 8
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 26
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 26
% 0.13/0.39  # Processed clauses                    : 80
% 0.13/0.39  # ...of these trivial                  : 0
% 0.13/0.39  # ...subsumed                          : 0
% 0.13/0.39  # ...remaining for further processing  : 80
% 0.13/0.39  # Other redundant clauses eliminated   : 1
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 4
% 0.13/0.39  # Generated clauses                    : 32
% 0.13/0.39  # ...of the previous two non-trivial   : 32
% 0.13/0.39  # Contextual simplify-reflections      : 2
% 0.13/0.39  # Paramodulations                      : 31
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 1
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
% 0.13/0.39  # Current number of processed clauses  : 49
% 0.13/0.39  #    Positive orientable unit clauses  : 15
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 7
% 0.13/0.39  #    Non-unit-clauses                  : 27
% 0.13/0.39  # Current number of unprocessed clauses: 4
% 0.13/0.39  # ...number of literals in the above   : 16
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 30
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 299
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 35
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.39  # Unit Clause-clause subsumption calls : 14
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 5
% 0.13/0.39  # BW rewrite match successes           : 2
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 4773
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.041 s
% 0.13/0.39  # System time              : 0.008 s
% 0.13/0.39  # Total time               : 0.049 s
% 0.13/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
