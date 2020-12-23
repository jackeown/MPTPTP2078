%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t54_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 181 expanded)
%              Number of clauses        :   33 (  55 expanded)
%              Number of leaves         :    6 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  271 (2422 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t54_tmap_1,conjecture,(
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
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X3,X1,X4,X6)
                              & v5_pre_topc(X5,X1,X2) )
                           => r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t54_tmap_1)).

fof(dt_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => m1_subset_1(k3_funct_2(X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',dt_k3_funct_2)).

fof(t52_tmap_1,axiom,(
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
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X3))
                             => ( ( X7 = k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)
                                  & r1_tmap_1(X2,X3,X4,X6)
                                  & r1_tmap_1(X3,X1,X5,X7) )
                               => r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t52_tmap_1)).

fof(t49_tmap_1,axiom,(
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
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',t49_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t54_tmap_1.p',dt_l1_pre_topc)).

fof(c_0_6,negated_conjecture,(
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
                  & v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X3))
                           => ( ( r1_tmap_1(X3,X1,X4,X6)
                                & v5_pre_topc(X5,X1,X2) )
                             => r1_tmap_1(X3,X2,k1_partfun1(u1_struct_0(X3),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X2),X4,X5),X6) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t54_tmap_1])).

fof(c_0_7,plain,(
    ! [X22,X23,X24,X25] :
      ( v1_xboole_0(X22)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,X22,X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | ~ m1_subset_1(X25,X22)
      | m1_subset_1(k3_funct_2(X22,X23,X24,X25),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_funct_2])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & r1_tmap_1(esk3_0,esk1_0,esk4_0,esk6_0)
    & v5_pre_topc(esk5_0,esk1_0,esk2_0)
    & ~ r1_tmap_1(esk3_0,esk2_0,k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0,esk5_0),esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_6])])])])).

fof(c_0_9,plain,(
    ! [X57,X58,X59,X60,X61,X62,X63] :
      ( v2_struct_0(X57)
      | ~ v2_pre_topc(X57)
      | ~ l1_pre_topc(X57)
      | v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X59)
      | ~ v2_pre_topc(X59)
      | ~ l1_pre_topc(X59)
      | ~ v1_funct_1(X60)
      | ~ v1_funct_2(X60,u1_struct_0(X58),u1_struct_0(X59))
      | ~ m1_subset_1(X60,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X58),u1_struct_0(X59))))
      | ~ v1_funct_1(X61)
      | ~ v1_funct_2(X61,u1_struct_0(X59),u1_struct_0(X57))
      | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X59),u1_struct_0(X57))))
      | ~ m1_subset_1(X62,u1_struct_0(X58))
      | ~ m1_subset_1(X63,u1_struct_0(X59))
      | X63 != k3_funct_2(u1_struct_0(X58),u1_struct_0(X59),X60,X62)
      | ~ r1_tmap_1(X58,X59,X60,X62)
      | ~ r1_tmap_1(X59,X57,X61,X63)
      | r1_tmap_1(X58,X57,k1_partfun1(u1_struct_0(X58),u1_struct_0(X59),u1_struct_0(X59),u1_struct_0(X57),X60,X61),X62) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t52_tmap_1])])])])).

fof(c_0_10,plain,(
    ! [X49,X50,X51,X52] :
      ( ( ~ v5_pre_topc(X51,X50,X49)
        | ~ m1_subset_1(X52,u1_struct_0(X50))
        | r1_tmap_1(X50,X49,X51,X52)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( m1_subset_1(esk10_3(X49,X50,X51),u1_struct_0(X50))
        | v5_pre_topc(X51,X50,X49)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ r1_tmap_1(X50,X49,X51,esk10_3(X49,X50,X51))
        | v5_pre_topc(X51,X50,X49)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_tmap_1])])])])])])).

cnf(c_0_11,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k3_funct_2(X1,X3,X2,X4),X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r1_tmap_1(X2,X1,k1_partfun1(u1_struct_0(X2),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X1),X4,X5),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ m1_subset_1(X6,u1_struct_0(X2))
    | ~ m1_subset_1(X7,u1_struct_0(X3))
    | X7 != k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X6)
    | ~ r1_tmap_1(X2,X3,X4,X6)
    | ~ r1_tmap_1(X3,X1,X5,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r1_tmap_1(X2,X3,X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,X1),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( r1_tmap_1(X1,X2,k1_partfun1(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X3),u1_struct_0(X2),X4,X5),X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X5,k3_funct_2(u1_struct_0(X1),u1_struct_0(X3),X4,X6))
    | ~ r1_tmap_1(X1,X3,X4,X6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X3),X4,X6),u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk1_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_34,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24])]),c_0_25]),c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,esk6_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_36,plain,(
    ! [X72] :
      ( v2_struct_0(X72)
      | ~ l1_struct_0(X72)
      | ~ v1_xboole_0(u1_struct_0(X72)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_37,negated_conjecture,
    ( r1_tmap_1(esk3_0,X1,k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(X1),esk4_0,X2),esk6_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk1_0,X1,X2,k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,esk6_0))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk1_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_13]),c_0_28]),c_0_12]),c_0_14]),c_0_22]),c_0_31]),c_0_24]),c_0_32])]),c_0_33]),c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r1_tmap_1(esk1_0,esk2_0,esk5_0,k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk1_0),esk4_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,k1_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_23])]),c_0_39]),c_0_25]),c_0_35])).

fof(c_0_42,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | l1_struct_0(X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_43,negated_conjecture,
    ( ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_33])).

cnf(c_0_44,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_31])]),
    [proof]).
%------------------------------------------------------------------------------
