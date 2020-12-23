%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 418 expanded)
%              Number of clauses        :   40 ( 130 expanded)
%              Number of leaves         :    4 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  318 (6211 expanded)
%              Number of equality atoms :   16 ( 309 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t66_tmap_1,conjecture,(
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
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( v3_pre_topc(X5,X2)
                                  & r2_hidden(X6,X5)
                                  & r1_tarski(X5,u1_struct_0(X4))
                                  & X6 = X7 )
                               => ( r1_tmap_1(X2,X1,X3,X6)
                                <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tmap_1)).

fof(t55_tops_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( ( v3_pre_topc(X4,X2)
                     => k1_tops_1(X2,X4) = X4 )
                    & ( k1_tops_1(X1,X3) = X3
                     => v3_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(t65_tmap_1,axiom,(
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
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X2))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ( ( r1_tarski(X5,u1_struct_0(X4))
                                  & m1_connsp_2(X5,X2,X6)
                                  & X6 = X7 )
                               => ( r1_tmap_1(X2,X1,X3,X6)
                                <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1] :
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
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ( ( v3_pre_topc(X5,X2)
                                    & r2_hidden(X6,X5)
                                    & r1_tarski(X5,u1_struct_0(X4))
                                    & X6 = X7 )
                                 => ( r1_tmap_1(X2,X1,X3,X6)
                                  <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t66_tmap_1])).

fof(c_0_5,plain,(
    ! [X8,X9,X10,X11] :
      ( ( ~ v3_pre_topc(X11,X9)
        | k1_tops_1(X9,X11) = X11
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( k1_tops_1(X8,X10) != X10
        | v3_pre_topc(X10,X8)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk6_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & v3_pre_topc(esk5_0,esk2_0)
    & r2_hidden(esk6_0,esk5_0)
    & r1_tarski(esk5_0,u1_struct_0(esk4_0))
    & esk6_0 = esk7_0
    & ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
      | ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0) )
    & ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
      | r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21] :
      ( ( ~ r1_tmap_1(X16,X15,X17,X20)
        | r1_tmap_1(X18,X15,k2_tmap_1(X16,X15,X17,X18),X21)
        | ~ r1_tarski(X19,u1_struct_0(X18))
        | ~ m1_connsp_2(X19,X16,X20)
        | X20 != X21
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X16),u1_struct_0(X15))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r1_tmap_1(X18,X15,k2_tmap_1(X16,X15,X17,X18),X21)
        | r1_tmap_1(X16,X15,X17,X20)
        | ~ r1_tarski(X19,u1_struct_0(X18))
        | ~ m1_connsp_2(X19,X16,X20)
        | X20 != X21
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | ~ m1_subset_1(X20,u1_struct_0(X16))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))
        | v2_struct_0(X18)
        | ~ m1_pre_topc(X18,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X16),u1_struct_0(X15))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

cnf(c_0_8,plain,
    ( k1_tops_1(X2,X1) = X1
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,plain,
    ( r1_tmap_1(X3,X2,X4,X6)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ r1_tarski(X7,u1_struct_0(X1))
    | ~ m1_connsp_2(X7,X3,X6)
    | X6 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ( ~ m1_connsp_2(X14,X12,X13)
        | r2_hidden(X13,k1_tops_1(X12,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) )
      & ( ~ r2_hidden(X13,k1_tops_1(X12,X14))
        | m1_connsp_2(X14,X12,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ m1_subset_1(X13,u1_struct_0(X12))
        | v2_struct_0(X12)
        | ~ v2_pre_topc(X12)
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_14,negated_conjecture,
    ( k1_tops_1(esk2_0,esk5_0) = esk5_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ r1_tarski(X6,u1_struct_0(X5))
    | ~ m1_pre_topc(X5,X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X6,X1,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_24,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,negated_conjecture,
    ( k1_tops_1(esk2_0,esk5_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_10]),c_0_11]),c_0_15])])).

cnf(c_0_26,plain,
    ( r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)
    | v2_struct_0(X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ r1_tarski(X7,u1_struct_0(X5))
    | ~ m1_connsp_2(X7,X1,X4)
    | X4 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X5,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,X2),X1)
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_connsp_2(X3,esk2_0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19]),c_0_11]),c_0_20]),c_0_15]),c_0_21])]),c_0_22]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_31,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,X1)
    | ~ r2_hidden(X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_10]),c_0_11]),c_0_15])]),c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_35,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_36,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_37,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ r1_tarski(X6,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_connsp_2(X6,X3,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X3))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_39,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)
    | ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),X1)
    | ~ m1_connsp_2(esk5_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29]),c_0_10])]),c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( m1_connsp_2(esk5_0,esk2_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( r1_tmap_1(X1,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,X2)
    | ~ r1_tarski(X3,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_connsp_2(X3,esk2_0,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_11]),c_0_21]),c_0_15])]),c_0_23]),c_0_22])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_33]),c_0_41])]),c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),X1)
    | ~ r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)
    | ~ m1_connsp_2(esk5_0,esk2_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_28]),c_0_29]),c_0_10])]),c_0_30])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_45]),c_0_33]),c_0_41])]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.13/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.028 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t66_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>((((v3_pre_topc(X5,X2)&r2_hidden(X6,X5))&r1_tarski(X5,u1_struct_0(X4)))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_tmap_1)).
% 0.13/0.37  fof(t55_tops_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(l1_pre_topc(X2)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>((v3_pre_topc(X4,X2)=>k1_tops_1(X2,X4)=X4)&(k1_tops_1(X1,X3)=X3=>v3_pre_topc(X3,X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 0.13/0.37  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.13/0.37  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.13/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>((((v3_pre_topc(X5,X2)&r2_hidden(X6,X5))&r1_tarski(X5,u1_struct_0(X4)))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7))))))))))), inference(assume_negation,[status(cth)],[t66_tmap_1])).
% 0.13/0.37  fof(c_0_5, plain, ![X8, X9, X10, X11]:((~v3_pre_topc(X11,X9)|k1_tops_1(X9,X11)=X11|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X9)|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(k1_tops_1(X8,X10)!=X10|v3_pre_topc(X10,X8)|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X8)))|~l1_pre_topc(X9)|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_1])])])])).
% 0.13/0.37  fof(c_0_6, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk6_0,u1_struct_0(esk2_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&((((v3_pre_topc(esk5_0,esk2_0)&r2_hidden(esk6_0,esk5_0))&r1_tarski(esk5_0,u1_struct_0(esk4_0)))&esk6_0=esk7_0)&((~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0))&(r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.13/0.37  fof(c_0_7, plain, ![X15, X16, X17, X18, X19, X20, X21]:((~r1_tmap_1(X16,X15,X17,X20)|r1_tmap_1(X18,X15,k2_tmap_1(X16,X15,X17,X18),X21)|(~r1_tarski(X19,u1_struct_0(X18))|~m1_connsp_2(X19,X16,X20)|X20!=X21)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X16))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X16),u1_struct_0(X15))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~r1_tmap_1(X18,X15,k2_tmap_1(X16,X15,X17,X18),X21)|r1_tmap_1(X16,X15,X17,X20)|(~r1_tarski(X19,u1_struct_0(X18))|~m1_connsp_2(X19,X16,X20)|X20!=X21)|~m1_subset_1(X21,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X16))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X16)))|(v2_struct_0(X18)|~m1_pre_topc(X18,X16))|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X16),u1_struct_0(X15))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.13/0.37  cnf(c_0_8, plain, (k1_tops_1(X2,X1)=X1|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|~l1_pre_topc(X2)|~v2_pre_topc(X4)|~l1_pre_topc(X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.13/0.37  cnf(c_0_9, negated_conjecture, (v3_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_12, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  fof(c_0_13, plain, ![X12, X13, X14]:((~m1_connsp_2(X14,X12,X13)|r2_hidden(X13,k1_tops_1(X12,X14))|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))&(~r2_hidden(X13,k1_tops_1(X12,X14))|m1_connsp_2(X14,X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~m1_subset_1(X13,u1_struct_0(X12))|(v2_struct_0(X12)|~v2_pre_topc(X12)|~l1_pre_topc(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.13/0.37  cnf(c_0_14, negated_conjecture, (k1_tops_1(esk2_0,esk5_0)=esk5_0|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])])).
% 0.13/0.37  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_16, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~r1_tarski(X6,u1_struct_0(X5))|~m1_pre_topc(X5,X1)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X5))|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)), inference(er,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_17, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_21, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_24, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_25, negated_conjecture, (k1_tops_1(esk2_0,esk5_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_10]), c_0_11]), c_0_15])])).
% 0.13/0.37  cnf(c_0_26, plain, (r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X6)|v2_struct_0(X5)|v2_struct_0(X1)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,X3,X4)|~r1_tarski(X7,u1_struct_0(X5))|~m1_connsp_2(X7,X1,X4)|X4!=X6|~m1_subset_1(X6,u1_struct_0(X5))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X5,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.37  cnf(c_0_27, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,X2),X1)|~r1_tarski(X3,u1_struct_0(X2))|~m1_pre_topc(X2,esk2_0)|~m1_connsp_2(X3,esk2_0,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19]), c_0_11]), c_0_20]), c_0_15]), c_0_21])]), c_0_22]), c_0_23])).
% 0.13/0.37  cnf(c_0_28, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_31, negated_conjecture, (m1_connsp_2(esk5_0,esk2_0,X1)|~r2_hidden(X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_10]), c_0_11]), c_0_15])]), c_0_23])).
% 0.13/0.37  cnf(c_0_32, negated_conjecture, (r2_hidden(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_35, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_37, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,X2,X4,X5)|~r1_tarski(X6,u1_struct_0(X1))|~m1_pre_topc(X1,X3)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_connsp_2(X6,X3,X5)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X5,u1_struct_0(X3))|~l1_pre_topc(X2)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~v2_pre_topc(X3)), inference(er,[status(thm)],[c_0_26])).
% 0.13/0.37  cnf(c_0_38, negated_conjecture, (~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)|~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),X1)|~m1_connsp_2(esk5_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29]), c_0_10])]), c_0_30])).
% 0.13/0.37  cnf(c_0_40, negated_conjecture, (m1_connsp_2(esk5_0,esk2_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_34, c_0_35])).
% 0.13/0.37  cnf(c_0_42, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_36, c_0_35])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r1_tmap_1(X1,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk2_0,esk1_0,esk3_0,X2)|~r1_tarski(X3,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)|~m1_connsp_2(X3,esk2_0,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))|~m1_subset_1(X2,u1_struct_0(esk2_0))|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_11]), c_0_21]), c_0_15])]), c_0_23]), c_0_22])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_38, c_0_35])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r1_tmap_1(esk2_0,esk1_0,esk3_0,esk6_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_33]), c_0_41])]), c_0_42])).
% 0.13/0.37  cnf(c_0_46, negated_conjecture, (r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),X1)|~r1_tmap_1(esk2_0,esk1_0,esk3_0,X1)|~m1_connsp_2(esk5_0,esk2_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_28]), c_0_29]), c_0_10])]), c_0_30])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (~r1_tmap_1(esk4_0,esk1_0,k2_tmap_1(esk2_0,esk1_0,esk3_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45])])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_40]), c_0_45]), c_0_33]), c_0_41])]), c_0_47]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 49
% 0.13/0.37  # Proof object clause steps            : 40
% 0.13/0.37  # Proof object formula steps           : 9
% 0.13/0.37  # Proof object conjectures             : 37
% 0.13/0.37  # Proof object clause conjectures      : 34
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 24
% 0.13/0.37  # Proof object initial formulas used   : 4
% 0.13/0.37  # Proof object generating inferences   : 10
% 0.13/0.37  # Proof object simplifying inferences  : 55
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 4
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 26
% 0.13/0.37  # Removed in clause preprocessing      : 0
% 0.13/0.37  # Initial clauses in saturation        : 26
% 0.13/0.37  # Processed clauses                    : 64
% 0.13/0.37  # ...of these trivial                  : 0
% 0.13/0.37  # ...subsumed                          : 0
% 0.13/0.37  # ...remaining for further processing  : 64
% 0.13/0.37  # Other redundant clauses eliminated   : 2
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 0
% 0.13/0.37  # Backward-rewritten                   : 3
% 0.13/0.37  # Generated clauses                    : 14
% 0.13/0.37  # ...of the previous two non-trivial   : 12
% 0.13/0.37  # Contextual simplify-reflections      : 1
% 0.13/0.37  # Paramodulations                      : 12
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 2
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 33
% 0.13/0.37  #    Positive orientable unit clauses  : 18
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 4
% 0.13/0.37  #    Non-unit-clauses                  : 11
% 0.13/0.37  # Current number of unprocessed clauses: 0
% 0.13/0.37  # ...number of literals in the above   : 0
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 29
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 144
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 1
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.13/0.37  # Unit Clause-clause subsumption calls : 3
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 5
% 0.13/0.37  # BW rewrite match successes           : 2
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 3433
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.032 s
% 0.13/0.37  # System time              : 0.005 s
% 0.13/0.37  # Total time               : 0.036 s
% 0.13/0.37  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
