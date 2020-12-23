%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t90_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:21 EDT 2019

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 959 expanded)
%              Number of clauses        :   58 ( 286 expanded)
%              Number of leaves         :    5 ( 231 expanded)
%              Depth                    :   15
%              Number of atoms          :  484 (17458 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   64 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t90_tmap_1,conjecture,(
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
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X5,X3) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( ( v1_funct_1(k3_tmap_1(X1,X2,X4,X3,X6))
                                & v1_funct_2(k3_tmap_1(X1,X2,X4,X3,X6),u1_struct_0(X3),u1_struct_0(X2))
                                & v5_pre_topc(k3_tmap_1(X1,X2,X4,X3,X6),X3,X2)
                                & m1_subset_1(k3_tmap_1(X1,X2,X4,X3,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => ( v1_funct_1(k3_tmap_1(X1,X2,X4,X5,X6))
                                & v1_funct_2(k3_tmap_1(X1,X2,X4,X5,X6),u1_struct_0(X5),u1_struct_0(X2))
                                & v5_pre_topc(k3_tmap_1(X1,X2,X4,X5,X6),X5,X2)
                                & m1_subset_1(k3_tmap_1(X1,X2,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t90_tmap_1)).

fof(t79_tmap_1,axiom,(
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
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( ( m1_pre_topc(X4,X3)
                          & m1_pre_topc(X5,X4) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t79_tmap_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',dt_k3_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',redefinition_r2_funct_2)).

fof(t89_tmap_1,axiom,(
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
                        & v5_pre_topc(X5,X3,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
                          & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
                          & v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
                          & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t90_tmap_1.p',t89_tmap_1)).

fof(c_0_5,negated_conjecture,(
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
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X5,X3) )
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( ( v1_funct_1(k3_tmap_1(X1,X2,X4,X3,X6))
                                  & v1_funct_2(k3_tmap_1(X1,X2,X4,X3,X6),u1_struct_0(X3),u1_struct_0(X2))
                                  & v5_pre_topc(k3_tmap_1(X1,X2,X4,X3,X6),X3,X2)
                                  & m1_subset_1(k3_tmap_1(X1,X2,X4,X3,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                               => ( v1_funct_1(k3_tmap_1(X1,X2,X4,X5,X6))
                                  & v1_funct_2(k3_tmap_1(X1,X2,X4,X5,X6),u1_struct_0(X5),u1_struct_0(X2))
                                  & v5_pre_topc(k3_tmap_1(X1,X2,X4,X5,X6),X5,X2)
                                  & m1_subset_1(k3_tmap_1(X1,X2,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X2)))) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t90_tmap_1])).

fof(c_0_6,plain,(
    ! [X54,X55,X56,X57,X58,X59] :
      ( v2_struct_0(X54)
      | ~ v2_pre_topc(X54)
      | ~ l1_pre_topc(X54)
      | v2_struct_0(X55)
      | ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | v2_struct_0(X56)
      | ~ m1_pre_topc(X56,X54)
      | v2_struct_0(X57)
      | ~ m1_pre_topc(X57,X54)
      | v2_struct_0(X58)
      | ~ m1_pre_topc(X58,X54)
      | ~ m1_pre_topc(X57,X56)
      | ~ m1_pre_topc(X58,X57)
      | ~ v1_funct_1(X59)
      | ~ v1_funct_2(X59,u1_struct_0(X56),u1_struct_0(X55))
      | ~ m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X56),u1_struct_0(X55))))
      | r2_funct_2(u1_struct_0(X58),u1_struct_0(X55),k3_tmap_1(X54,X55,X57,X58,k3_tmap_1(X54,X55,X56,X57,X59)),k3_tmap_1(X54,X55,X56,X58,X59)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t79_tmap_1])])])])).

fof(c_0_7,negated_conjecture,
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
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & m1_pre_topc(esk3_0,esk4_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))
    & v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk3_0,esk2_0)
    & m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & ( ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))
      | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
      | ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
      | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X15,X16,X17,X18,X19] :
      ( ( v1_funct_1(k3_tmap_1(X15,X16,X17,X18,X19))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_pre_topc(X18,X15)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16)))) )
      & ( v1_funct_2(k3_tmap_1(X15,X16,X17,X18,X19),u1_struct_0(X18),u1_struct_0(X16))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_pre_topc(X18,X15)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16)))) )
      & ( m1_subset_1(k3_tmap_1(X15,X16,X17,X18,X19),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X18),u1_struct_0(X16))))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15)
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | ~ m1_pre_topc(X17,X15)
        | ~ m1_pre_topc(X18,X15)
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,u1_struct_0(X17),u1_struct_0(X16))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X17),u1_struct_0(X16)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X5)
    | r2_funct_2(u1_struct_0(X5),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X5,k3_tmap_1(X1,X2,X3,X4,X6)),k3_tmap_1(X1,X2,X3,X5,X6))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X5,X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X5,X4)
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(X2,esk2_0,X3,X1,k3_tmap_1(X2,esk2_0,esk4_0,X3,esk6_0)),k3_tmap_1(X2,esk2_0,esk4_0,X1,esk6_0))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X3,esk4_0)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15]),c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_23,plain,(
    ! [X29,X30,X31,X32] :
      ( ( ~ r2_funct_2(X29,X30,X31,X32)
        | X31 = X32
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) )
      & ( X31 != X32
        | r2_funct_2(X29,X30,X31,X32)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X29,X30)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X29,X30))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk2_0,esk4_0,X2,esk6_0),u1_struct_0(X2),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(X2,esk2_0,esk3_0,X1,k3_tmap_1(X2,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(X2,esk2_0,esk4_0,X1,esk6_0))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk4_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(esk3_0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,esk6_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,esk6_0),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_25]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_25]),c_0_32]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( X1 = k3_tmap_1(esk1_0,esk2_0,esk4_0,X2,esk6_0)
    | ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),X1,k3_tmap_1(esk1_0,esk2_0,esk4_0,X2,esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_pre_topc(X2,esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk5_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_41]),c_0_42]),c_0_43]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39])])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_32]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_41]),c_0_42]),c_0_43]),c_0_13]),c_0_14])]),c_0_15])).

fof(c_0_50,plain,(
    ! [X62,X63,X64,X65,X66] :
      ( ( v1_funct_1(k3_tmap_1(X62,X63,X64,X65,X66))
        | ~ m1_pre_topc(X65,X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,u1_struct_0(X64),u1_struct_0(X63))
        | ~ v5_pre_topc(X66,X64,X63)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X63))))
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X62)
        | v2_struct_0(X64)
        | ~ m1_pre_topc(X64,X62)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63)
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( v1_funct_2(k3_tmap_1(X62,X63,X64,X65,X66),u1_struct_0(X65),u1_struct_0(X63))
        | ~ m1_pre_topc(X65,X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,u1_struct_0(X64),u1_struct_0(X63))
        | ~ v5_pre_topc(X66,X64,X63)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X63))))
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X62)
        | v2_struct_0(X64)
        | ~ m1_pre_topc(X64,X62)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63)
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( v5_pre_topc(k3_tmap_1(X62,X63,X64,X65,X66),X65,X63)
        | ~ m1_pre_topc(X65,X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,u1_struct_0(X64),u1_struct_0(X63))
        | ~ v5_pre_topc(X66,X64,X63)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X63))))
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X62)
        | v2_struct_0(X64)
        | ~ m1_pre_topc(X64,X62)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63)
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) )
      & ( m1_subset_1(k3_tmap_1(X62,X63,X64,X65,X66),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X63))))
        | ~ m1_pre_topc(X65,X64)
        | ~ v1_funct_1(X66)
        | ~ v1_funct_2(X66,u1_struct_0(X64),u1_struct_0(X63))
        | ~ v5_pre_topc(X66,X64,X63)
        | ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X64),u1_struct_0(X63))))
        | v2_struct_0(X65)
        | ~ m1_pre_topc(X65,X62)
        | v2_struct_0(X64)
        | ~ m1_pre_topc(X64,X62)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63)
        | v2_struct_0(X62)
        | ~ v2_pre_topc(X62)
        | ~ l1_pre_topc(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t89_tmap_1])])])])])).

cnf(c_0_51,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_39])])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_32]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_41]),c_0_42]),c_0_43]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_54,plain,
    ( v5_pre_topc(k3_tmap_1(X1,X2,X3,X4,X5),X4,X2)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X4,X3)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v5_pre_topc(X5,X3,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0),esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_56,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_39])])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk3_0,X1,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_32]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(X1,esk2_0,esk3_0,X2,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),X2,esk2_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_41]),c_0_55]),c_0_42]),c_0_43]),c_0_13]),c_0_14])]),c_0_15]),c_0_22])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0))
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
    | ~ m1_subset_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)) = k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_39])])).

cnf(c_0_61,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(X1,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),esk5_0,esk2_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_38]),c_0_40])).

cnf(c_0_62,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_34]),c_0_39])])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_60]),c_0_41]),c_0_42]),c_0_43]),c_0_39]),c_0_32]),c_0_13]),c_0_26]),c_0_14]),c_0_27])]),c_0_28]),c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0,k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk6_0)),esk5_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_32]),c_0_39]),c_0_26]),c_0_27])]),c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( ~ v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0)
    | ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_66,negated_conjecture,
    ( v5_pre_topc(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),esk5_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_funct_2(k3_tmap_1(esk1_0,esk2_0,esk4_0,esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_65,c_0_66])])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_36]),c_0_39])]),
    [proof]).
%------------------------------------------------------------------------------
