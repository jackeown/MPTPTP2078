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
% DateTime   : Thu Dec  3 11:17:43 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (1974 expanded)
%              Number of clauses        :   51 ( 660 expanded)
%              Number of leaves         :    7 ( 454 expanded)
%              Depth                    :   16
%              Number of atoms          :  296 (31112 expanded)
%              Number of equality atoms :   27 (1510 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   25 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t80_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ! [X7] :
                              ( ( v1_funct_1(X7)
                                & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( X4 = X1
                                  & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                               => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tmap_1)).

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

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

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
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ! [X7] :
                                ( ( v1_funct_1(X7)
                                  & v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                               => ( ( X4 = X1
                                    & r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7) )
                                 => ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)
                                  <=> r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t80_tmap_1])).

fof(c_0_8,negated_conjecture,
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
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & esk4_0 = esk1_0
    & r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)
    & ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
      | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) )
    & ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
      | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).

fof(c_0_9,plain,(
    ! [X23,X24,X25,X26,X27] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X23)
      | ~ m1_pre_topc(X26,X23)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X24))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))
      | ~ m1_pre_topc(X26,X25)
      | k3_tmap_1(X23,X24,X25,X26,X27) = k2_partfun1(u1_struct_0(X25),u1_struct_0(X24),X27,u1_struct_0(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_10,plain,(
    ! [X28,X29,X30] :
      ( ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | ~ m1_pre_topc(X30,X29)
      | m1_pre_topc(X30,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_11,plain,(
    ! [X19,X20,X21,X22] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ v1_funct_1(X21)
      | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
      | ~ m1_pre_topc(X22,X19)
      | k2_tmap_1(X19,X20,X21,X22) = k2_partfun1(u1_struct_0(X19),u1_struct_0(X20),X21,u1_struct_0(X22)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( esk4_0 = esk1_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_14,c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk7_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk7_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_18]),c_0_19]),c_0_21]),c_0_23]),c_0_24])]),c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(esk3_0)) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_33,plain,(
    ! [X13,X14,X15,X16,X17,X18] :
      ( ( ~ r1_funct_2(X13,X14,X15,X16,X17,X18)
        | X17 = X18
        | v1_xboole_0(X14)
        | v1_xboole_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X13,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != X18
        | r1_funct_2(X13,X14,X15,X16,X17,X18)
        | v1_xboole_0(X14)
        | v1_xboole_0(X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X13,X14)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_29]),c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(rw,[status(thm)],[c_0_32,c_0_13])).

cnf(c_0_38,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_39,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_44,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0) = k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20]),c_0_22])]),c_0_26])).

fof(c_0_46,plain,(
    ! [X10,X11,X12] :
      ( ~ v1_xboole_0(X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X10)))
      | v1_xboole_0(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_47,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_13])).

cnf(c_0_48,negated_conjecture,
    ( esk7_0 = esk5_0
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_18]),c_0_41]),c_0_23]),c_0_42]),c_0_24]),c_0_43])])).

cnf(c_0_49,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

fof(c_0_54,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | X8 = X9
      | ~ v1_xboole_0(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(esk7_0)
    | ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_24])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( esk7_0 = esk5_0 ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_63,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0) ),
    inference(rw,[status(thm)],[c_0_47,c_0_45])).

cnf(c_0_64,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49,c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_62])]),c_0_64]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.44  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.028 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t80_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_tmap_1)).
% 0.20/0.44  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.44  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.20/0.44  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.44  fof(redefinition_r1_funct_2, axiom, ![X1, X2, X3, X4, X5, X6]:((((((((~(v1_xboole_0(X2))&~(v1_xboole_0(X4)))&v1_funct_1(X5))&v1_funct_2(X5,X1,X2))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&v1_funct_2(X6,X3,X4))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(r1_funct_2(X1,X2,X3,X4,X5,X6)<=>X5=X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 0.20/0.44  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.20/0.44  fof(t8_boole, axiom, ![X1, X2]:~(((v1_xboole_0(X1)&X1!=X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 0.20/0.44  fof(c_0_7, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>![X7]:(((v1_funct_1(X7)&v1_funct_2(X7,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>((X4=X1&r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4),u1_struct_0(X2),X5,X7))=>(r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X7),X6)<=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k2_tmap_1(X1,X2,X5,X3),X6))))))))))), inference(assume_negation,[status(cth)],[t80_tmap_1])).
% 0.20/0.44  fof(c_0_8, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&((esk4_0=esk1_0&r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0))&((~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0))&(r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_7])])])])).
% 0.20/0.44  fof(c_0_9, plain, ![X23, X24, X25, X26, X27]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_pre_topc(X25,X23)|(~m1_pre_topc(X26,X23)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X25),u1_struct_0(X24))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X25),u1_struct_0(X24))))|(~m1_pre_topc(X26,X25)|k3_tmap_1(X23,X24,X25,X26,X27)=k2_partfun1(u1_struct_0(X25),u1_struct_0(X24),X27,u1_struct_0(X26)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.44  fof(c_0_10, plain, ![X28, X29, X30]:(~v2_pre_topc(X28)|~l1_pre_topc(X28)|(~m1_pre_topc(X29,X28)|(~m1_pre_topc(X30,X29)|m1_pre_topc(X30,X28)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.20/0.44  fof(c_0_11, plain, ![X19, X20, X21, X22]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))|(~m1_pre_topc(X22,X19)|k2_tmap_1(X19,X20,X21,X22)=k2_partfun1(u1_struct_0(X19),u1_struct_0(X20),X21,u1_struct_0(X22)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.44  cnf(c_0_12, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_13, negated_conjecture, (esk4_0=esk1_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_14, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.44  cnf(c_0_16, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.44  cnf(c_0_17, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.44  cnf(c_0_18, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.20/0.44  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[c_0_14, c_0_13])).
% 0.20/0.44  cnf(c_0_25, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_27, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.44  cnf(c_0_28, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk7_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24])]), c_0_25]), c_0_26])).
% 0.20/0.44  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_30, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk7_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_18]), c_0_19]), c_0_21]), c_0_23]), c_0_24])]), c_0_25])).
% 0.20/0.44  cnf(c_0_31, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk7_0,u1_struct_0(esk3_0))=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.44  cnf(c_0_32, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  fof(c_0_33, plain, ![X13, X14, X15, X16, X17, X18]:((~r1_funct_2(X13,X14,X15,X16,X17,X18)|X17=X18|(v1_xboole_0(X14)|v1_xboole_0(X16)|~v1_funct_1(X17)|~v1_funct_2(X17,X13,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(X17!=X18|r1_funct_2(X13,X14,X15,X16,X17,X18)|(v1_xboole_0(X14)|v1_xboole_0(X16)|~v1_funct_1(X17)|~v1_funct_2(X17,X13,X14)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).
% 0.20/0.44  cnf(c_0_34, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_35, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_36, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_29]), c_0_31])).
% 0.20/0.44  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(rw,[status(thm)],[c_0_32, c_0_13])).
% 0.20/0.44  cnf(c_0_38, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_39, plain, (X5=X6|v1_xboole_0(X2)|v1_xboole_0(X4)|~r1_funct_2(X1,X2,X3,X4,X5,X6)|~v1_funct_1(X5)|~v1_funct_2(X5,X1,X2)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~v1_funct_2(X6,X3,X4)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.44  cnf(c_0_40, negated_conjecture, (r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk7_0)), inference(rw,[status(thm)],[c_0_34, c_0_13])).
% 0.20/0.44  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_42, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.44  cnf(c_0_44, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_35, c_0_13])).
% 0.20/0.44  cnf(c_0_45, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0)=k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_20]), c_0_22])]), c_0_26])).
% 0.20/0.44  fof(c_0_46, plain, ![X10, X11, X12]:(~v1_xboole_0(X10)|(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X11,X10)))|v1_xboole_0(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.20/0.44  cnf(c_0_47, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk7_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_38, c_0_13])).
% 0.20/0.44  cnf(c_0_48, negated_conjecture, (esk7_0=esk5_0|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_18]), c_0_41]), c_0_23]), c_0_42]), c_0_24]), c_0_43])])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.44  cnf(c_0_50, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.44  cnf(c_0_51, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.44  cnf(c_0_52, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk3_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_45, c_0_48])).
% 0.20/0.44  cnf(c_0_53, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 0.20/0.44  fof(c_0_54, plain, ![X8, X9]:(~v1_xboole_0(X8)|X8=X9|~v1_xboole_0(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).
% 0.20/0.44  cnf(c_0_55, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_43])).
% 0.20/0.44  cnf(c_0_56, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])).
% 0.20/0.44  cnf(c_0_57, plain, (X1=X2|~v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.20/0.44  cnf(c_0_58, negated_conjecture, (v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 0.20/0.44  cnf(c_0_59, negated_conjecture, (v1_xboole_0(esk7_0)|~v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_50, c_0_24])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, (esk5_0=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.20/0.44  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_56])])).
% 0.20/0.44  cnf(c_0_62, negated_conjecture, (esk7_0=esk5_0), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.44  cnf(c_0_63, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk7_0,esk3_0),esk6_0)), inference(rw,[status(thm)],[c_0_47, c_0_45])).
% 0.20/0.44  cnf(c_0_64, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_49, c_0_62])])).
% 0.20/0.44  cnf(c_0_65, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_62])]), c_0_64]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 66
% 0.20/0.44  # Proof object clause steps            : 51
% 0.20/0.44  # Proof object formula steps           : 15
% 0.20/0.44  # Proof object conjectures             : 47
% 0.20/0.44  # Proof object clause conjectures      : 44
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 24
% 0.20/0.44  # Proof object initial formulas used   : 7
% 0.20/0.44  # Proof object generating inferences   : 14
% 0.20/0.44  # Proof object simplifying inferences  : 46
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 7
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 30
% 0.20/0.44  # Removed in clause preprocessing      : 0
% 0.20/0.44  # Initial clauses in saturation        : 30
% 0.20/0.44  # Processed clauses                    : 819
% 0.20/0.44  # ...of these trivial                  : 2
% 0.20/0.44  # ...subsumed                          : 524
% 0.20/0.44  # ...remaining for further processing  : 292
% 0.20/0.44  # Other redundant clauses eliminated   : 1
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 0
% 0.20/0.44  # Backward-rewritten                   : 161
% 0.20/0.44  # Generated clauses                    : 1572
% 0.20/0.44  # ...of the previous two non-trivial   : 1682
% 0.20/0.44  # Contextual simplify-reflections      : 6
% 0.20/0.44  # Paramodulations                      : 1571
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 1
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 101
% 0.20/0.44  #    Positive orientable unit clauses  : 21
% 0.20/0.44  #    Positive unorientable unit clauses: 0
% 0.20/0.44  #    Negative unit clauses             : 4
% 0.20/0.44  #    Non-unit-clauses                  : 76
% 0.20/0.44  # Current number of unprocessed clauses: 922
% 0.20/0.44  # ...number of literals in the above   : 5833
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 190
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 13816
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 2296
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 529
% 0.20/0.44  # Unit Clause-clause subsumption calls : 95
% 0.20/0.44  # Rewrite failures with RHS unbound    : 0
% 0.20/0.44  # BW rewrite match attempts            : 24
% 0.20/0.44  # BW rewrite match successes           : 6
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 40328
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.091 s
% 0.20/0.44  # System time              : 0.003 s
% 0.20/0.44  # Total time               : 0.094 s
% 0.20/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
