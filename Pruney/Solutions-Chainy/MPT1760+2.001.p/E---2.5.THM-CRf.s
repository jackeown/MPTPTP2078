%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:32 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 490 expanded)
%              Number of clauses        :   55 ( 166 expanded)
%              Number of leaves         :    9 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  374 (7602 expanded)
%              Number of equality atoms :    5 (  15 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t71_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & v5_pre_topc(X5,X2,X3)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                         => ( ( v1_funct_1(k2_tmap_1(X1,X2,X6,X4))
                              & v1_funct_2(k2_tmap_1(X1,X2,X6,X4),u1_struct_0(X4),u1_struct_0(X2))
                              & v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2)
                              & m1_subset_1(k2_tmap_1(X1,X2,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                           => ( v1_funct_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4))
                              & v1_funct_2(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),u1_struct_0(X4),u1_struct_0(X3))
                              & v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3)
                              & m1_subset_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_tmap_1)).

fof(t70_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                         => ( ( v5_pre_topc(X5,X2,X3)
                              & v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2) )
                           => v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tmap_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(fc8_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v1_xboole_0(X2)
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X5)
        & v1_funct_2(X5,X2,X3)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ( v1_funct_1(k5_relat_1(X4,X5))
        & v1_funct_2(k5_relat_1(X4,X5),X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_9,negated_conjecture,(
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
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & v5_pre_topc(X5,X2,X3)
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                           => ( ( v1_funct_1(k2_tmap_1(X1,X2,X6,X4))
                                & v1_funct_2(k2_tmap_1(X1,X2,X6,X4),u1_struct_0(X4),u1_struct_0(X2))
                                & v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2)
                                & m1_subset_1(k2_tmap_1(X1,X2,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                             => ( v1_funct_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4))
                                & v1_funct_2(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),u1_struct_0(X4),u1_struct_0(X3))
                                & v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3)
                                & m1_subset_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3)))) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_tmap_1])).

fof(c_0_10,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( v2_struct_0(X32)
      | ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X35)
      | ~ m1_pre_topc(X35,X32)
      | ~ v1_funct_1(X36)
      | ~ v1_funct_2(X36,u1_struct_0(X33),u1_struct_0(X34))
      | ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,u1_struct_0(X32),u1_struct_0(X33))
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))
      | ~ v5_pre_topc(X36,X33,X34)
      | ~ v5_pre_topc(k2_tmap_1(X32,X33,X37,X35),X35,X33)
      | v5_pre_topc(k2_tmap_1(X32,X34,k1_partfun1(u1_struct_0(X32),u1_struct_0(X33),u1_struct_0(X33),u1_struct_0(X34),X37,X36),X35),X35,X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tmap_1])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & v5_pre_topc(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0))
    & v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    & v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),esk4_0,esk2_0)
    & m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    & ( ~ v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))
      | ~ v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
      | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

fof(c_0_12,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ~ v1_funct_1(X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ v1_funct_1(X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k1_partfun1(X18,X19,X20,X21,X22,X23) = k5_relat_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).

cnf(c_0_13,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v5_pre_topc(X5,X2,X3)
    | ~ v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X13,X14,X15,X16,X17] :
      ( ( v1_funct_1(k5_relat_1(X16,X17))
        | v1_xboole_0(X14)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v1_funct_2(k5_relat_1(X16,X17),X13,X15)
        | v1_xboole_0(X14)
        | ~ v1_funct_1(X16)
        | ~ v1_funct_2(X16,X13,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,X14,X15)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).

cnf(c_0_20,plain,
    ( k1_partfun1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X7,X8,X9,X10,X11,X12] :
      ( ( v1_funct_1(k1_partfun1(X7,X8,X9,X10,X11,X12))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) )
      & ( m1_subset_1(k1_partfun1(X7,X8,X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(X11)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).

cnf(c_0_24,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,X1,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),esk4_0),esk4_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,X2,X3,esk4_0),esk4_0,X2)
    | ~ v5_pre_topc(X4,X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X3,u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X4) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_15]),c_0_16])]),c_0_17]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,plain,
    ( v1_funct_2(k5_relat_1(X1,X2),X3,X4)
    | v1_xboole_0(X5)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X5,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( k1_partfun1(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk3_0),X3,esk5_0) = k5_relat_1(X3,esk5_0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_37,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_39,plain,
    ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_40,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | l1_pre_topc(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_41,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,esk5_0),esk4_0),esk4_0,esk3_0)
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,X1,esk4_0),esk4_0,esk2_0)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_21]),c_0_22])]),c_0_31]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_44,plain,(
    ! [X28,X29,X30,X31] :
      ( ( v1_funct_1(k2_tmap_1(X28,X29,X30,X31))
        | ~ l1_struct_0(X28)
        | ~ l1_struct_0(X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ l1_struct_0(X31) )
      & ( v1_funct_2(k2_tmap_1(X28,X29,X30,X31),u1_struct_0(X31),u1_struct_0(X29))
        | ~ l1_struct_0(X28)
        | ~ l1_struct_0(X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ l1_struct_0(X31) )
      & ( m1_subset_1(k2_tmap_1(X28,X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29))))
        | ~ l1_struct_0(X28)
        | ~ l1_struct_0(X29)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ l1_struct_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_45,negated_conjecture,
    ( v1_funct_2(k5_relat_1(X1,esk5_0),X2,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,X2,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk2_0))))
    | ~ v1_funct_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_21]),c_0_22])])).

cnf(c_0_46,negated_conjecture,
    ( k5_relat_1(esk6_0,esk5_0) = k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(k1_partfun1(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk3_0),X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_22])])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k1_partfun1(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk3_0),X3,esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_21]),c_0_22])])).

cnf(c_0_50,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_35]),c_0_36])])).

cnf(c_0_53,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_46]),c_0_35]),c_0_36])])).

cnf(c_0_55,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_16])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_35]),c_0_36])])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_35]),c_0_36])])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_14]),c_0_16])])).

cnf(c_0_60,negated_conjecture,
    ( ~ v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_62,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_59])).

cnf(c_0_63,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_64,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_66,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_67,plain,(
    ! [X27] :
      ( v2_struct_0(X27)
      | ~ l1_struct_0(X27)
      | ~ v1_xboole_0(u1_struct_0(X27)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_62])])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1))
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_54]),c_0_55]),c_0_56]),c_0_57]),c_0_58])])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_71,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_62])])).

cnf(c_0_72,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_29])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.37/0.56  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.37/0.56  # and selection function SelectCQIPrecWNTNp.
% 0.37/0.56  #
% 0.37/0.56  # Preprocessing time       : 0.047 s
% 0.37/0.56  # Presaturation interreduction done
% 0.37/0.56  
% 0.37/0.56  # Proof found!
% 0.37/0.56  # SZS status Theorem
% 0.37/0.56  # SZS output start CNFRefutation
% 0.37/0.56  fof(t71_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)))&v5_pre_topc(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_funct_1(k2_tmap_1(X1,X2,X6,X4))&v1_funct_2(k2_tmap_1(X1,X2,X6,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((v1_funct_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4))&v1_funct_2(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),u1_struct_0(X4),u1_struct_0(X3)))&v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3))&m1_subset_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_tmap_1)).
% 0.37/0.56  fof(t70_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((v5_pre_topc(X5,X2,X3)&v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2))=>v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_tmap_1)).
% 0.37/0.56  fof(redefinition_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k1_partfun1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 0.37/0.56  fof(fc8_funct_2, axiom, ![X1, X2, X3, X4, X5]:(((((((~(v1_xboole_0(X2))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X5))&v1_funct_2(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>(v1_funct_1(k5_relat_1(X4,X5))&v1_funct_2(k5_relat_1(X4,X5),X1,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_2)).
% 0.37/0.56  fof(dt_k1_partfun1, axiom, ![X1, X2, X3, X4, X5, X6]:((((v1_funct_1(X5)&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X6))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>(v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))&m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 0.37/0.56  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.37/0.56  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.37/0.56  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.37/0.56  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.37/0.56  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((~(v2_struct_0(X3))&v2_pre_topc(X3))&l1_pre_topc(X3))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3)))&v5_pre_topc(X5,X2,X3))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_funct_1(k2_tmap_1(X1,X2,X6,X4))&v1_funct_2(k2_tmap_1(X1,X2,X6,X4),u1_struct_0(X4),u1_struct_0(X2)))&v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2))&m1_subset_1(k2_tmap_1(X1,X2,X6,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(((v1_funct_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4))&v1_funct_2(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),u1_struct_0(X4),u1_struct_0(X3)))&v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3))&m1_subset_1(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X3))))))))))))), inference(assume_negation,[status(cth)],[t71_tmap_1])).
% 0.37/0.56  fof(c_0_10, plain, ![X32, X33, X34, X35, X36, X37]:(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(v2_struct_0(X35)|~m1_pre_topc(X35,X32)|(~v1_funct_1(X36)|~v1_funct_2(X36,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X32),u1_struct_0(X33))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X33))))|(~v5_pre_topc(X36,X33,X34)|~v5_pre_topc(k2_tmap_1(X32,X33,X37,X35),X35,X33)|v5_pre_topc(k2_tmap_1(X32,X34,k1_partfun1(u1_struct_0(X32),u1_struct_0(X33),u1_struct_0(X33),u1_struct_0(X34),X37,X36),X35),X35,X34)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_tmap_1])])])])).
% 0.37/0.56  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&v5_pre_topc(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((((v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0))&v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0)))&v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),esk4_0,esk2_0))&m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))))&(~v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0)))))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.37/0.56  fof(c_0_12, plain, ![X18, X19, X20, X21, X22, X23]:(~v1_funct_1(X22)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|~v1_funct_1(X23)|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k1_partfun1(X18,X19,X20,X21,X22,X23)=k5_relat_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_partfun1])])).
% 0.37/0.56  cnf(c_0_13, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|v5_pre_topc(k2_tmap_1(X1,X3,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X3),X6,X5),X4),X4,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v5_pre_topc(X5,X2,X3)|~v5_pre_topc(k2_tmap_1(X1,X2,X6,X4),X4,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.37/0.56  cnf(c_0_14, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_15, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_16, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_17, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  fof(c_0_19, plain, ![X13, X14, X15, X16, X17]:((v1_funct_1(k5_relat_1(X16,X17))|(v1_xboole_0(X14)|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))&(v1_funct_2(k5_relat_1(X16,X17),X13,X15)|(v1_xboole_0(X14)|~v1_funct_1(X16)|~v1_funct_2(X16,X13,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|~v1_funct_1(X17)|~v1_funct_2(X17,X14,X15)|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_funct_2])])])])).
% 0.37/0.56  cnf(c_0_20, plain, (k1_partfun1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.37/0.56  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  fof(c_0_23, plain, ![X7, X8, X9, X10, X11, X12]:((v1_funct_1(k1_partfun1(X7,X8,X9,X10,X11,X12))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))&(m1_subset_1(k1_partfun1(X7,X8,X9,X10,X11,X12),k1_zfmisc_1(k2_zfmisc_1(X7,X10)))|(~v1_funct_1(X11)|~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|~v1_funct_1(X12)|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_partfun1])])])).
% 0.37/0.56  cnf(c_0_24, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,X1,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X1),X3,X4),esk4_0),esk4_0,X1)|v2_struct_0(X2)|v2_struct_0(X1)|~v5_pre_topc(k2_tmap_1(esk1_0,X2,X3,esk4_0),esk4_0,X2)|~v5_pre_topc(X4,X2,X1)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v1_funct_2(X3,u1_struct_0(esk1_0),u1_struct_0(X2))|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~v1_funct_1(X3)|~v1_funct_1(X4)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_15]), c_0_16])]), c_0_17]), c_0_18])).
% 0.37/0.56  cnf(c_0_25, negated_conjecture, (v5_pre_topc(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_26, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_29, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_33, plain, (v1_funct_2(k5_relat_1(X1,X2),X3,X4)|v1_xboole_0(X5)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))|~v1_funct_1(X2)|~v1_funct_2(X2,X5,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.37/0.56  cnf(c_0_34, negated_conjecture, (k1_partfun1(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk3_0),X3,esk5_0)=k5_relat_1(X3,esk5_0)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.37/0.56  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  fof(c_0_37, plain, ![X24]:(~l1_pre_topc(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.37/0.56  cnf(c_0_38, plain, (m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.56  cnf(c_0_39, plain, (v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X6)|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.37/0.56  fof(c_0_40, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|l1_pre_topc(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.37/0.56  cnf(c_0_41, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,esk5_0),esk4_0),esk4_0,esk3_0)|~v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,X1,esk4_0),esk4_0,esk2_0)|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))|~v1_funct_1(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_21]), c_0_22])]), c_0_31]), c_0_32])).
% 0.37/0.56  cnf(c_0_42, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk2_0,esk6_0,esk4_0),esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  fof(c_0_44, plain, ![X28, X29, X30, X31]:(((v1_funct_1(k2_tmap_1(X28,X29,X30,X31))|(~l1_struct_0(X28)|~l1_struct_0(X29)|~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|~l1_struct_0(X31)))&(v1_funct_2(k2_tmap_1(X28,X29,X30,X31),u1_struct_0(X31),u1_struct_0(X29))|(~l1_struct_0(X28)|~l1_struct_0(X29)|~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|~l1_struct_0(X31))))&(m1_subset_1(k2_tmap_1(X28,X29,X30,X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X29))))|(~l1_struct_0(X28)|~l1_struct_0(X29)|~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|~l1_struct_0(X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.37/0.56  cnf(c_0_45, negated_conjecture, (v1_funct_2(k5_relat_1(X1,esk5_0),X2,u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~v1_funct_2(X1,X2,u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,u1_struct_0(esk2_0))))|~v1_funct_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_30]), c_0_21]), c_0_22])])).
% 0.37/0.56  cnf(c_0_46, negated_conjecture, (k5_relat_1(esk6_0,esk5_0)=k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.37/0.56  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.37/0.56  cnf(c_0_48, negated_conjecture, (m1_subset_1(k1_partfun1(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk3_0),X3,esk5_0),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk3_0))))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_22])])).
% 0.37/0.56  cnf(c_0_49, negated_conjecture, (v1_funct_1(k1_partfun1(X1,X2,u1_struct_0(esk2_0),u1_struct_0(esk3_0),X3,esk5_0))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_21]), c_0_22])])).
% 0.37/0.56  cnf(c_0_50, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.37/0.56  cnf(c_0_51, negated_conjecture, (~v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))|~v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.37/0.56  cnf(c_0_52, negated_conjecture, (v5_pre_topc(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_35]), c_0_36])])).
% 0.37/0.56  cnf(c_0_53, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.56  cnf(c_0_54, negated_conjecture, (v1_funct_2(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_43]), c_0_46]), c_0_35]), c_0_36])])).
% 0.37/0.56  cnf(c_0_55, negated_conjecture, (l1_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_47, c_0_28])).
% 0.37/0.56  cnf(c_0_56, negated_conjecture, (l1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_47, c_0_16])).
% 0.37/0.56  cnf(c_0_57, negated_conjecture, (m1_subset_1(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_35]), c_0_36])])).
% 0.37/0.56  cnf(c_0_58, negated_conjecture, (v1_funct_1(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_35]), c_0_36])])).
% 0.37/0.56  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_14]), c_0_16])])).
% 0.37/0.56  cnf(c_0_60, negated_conjecture, (~v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.37/0.56  cnf(c_0_61, negated_conjecture, (v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])])).
% 0.37/0.56  cnf(c_0_62, negated_conjecture, (l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_47, c_0_59])).
% 0.37/0.56  cnf(c_0_63, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.56  cnf(c_0_64, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk3_0))))|~v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.37/0.56  cnf(c_0_65, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])])).
% 0.37/0.56  cnf(c_0_66, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.37/0.56  fof(c_0_67, plain, ![X27]:(v2_struct_0(X27)|~l1_struct_0(X27)|~v1_xboole_0(u1_struct_0(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.37/0.56  cnf(c_0_68, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_62])])).
% 0.37/0.56  cnf(c_0_69, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|v1_funct_1(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1))|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_54]), c_0_55]), c_0_56]), c_0_57]), c_0_58])])).
% 0.37/0.56  cnf(c_0_70, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.37/0.56  cnf(c_0_71, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_62])])).
% 0.37/0.56  cnf(c_0_72, negated_conjecture, (l1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_47, c_0_29])).
% 0.37/0.56  cnf(c_0_73, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])]), c_0_31]), ['proof']).
% 0.37/0.56  # SZS output end CNFRefutation
% 0.37/0.56  # Proof object total steps             : 74
% 0.37/0.56  # Proof object clause steps            : 55
% 0.37/0.56  # Proof object formula steps           : 19
% 0.37/0.56  # Proof object conjectures             : 47
% 0.37/0.56  # Proof object clause conjectures      : 44
% 0.37/0.56  # Proof object formula conjectures     : 3
% 0.37/0.56  # Proof object initial clauses used    : 31
% 0.37/0.56  # Proof object initial formulas used   : 9
% 0.37/0.56  # Proof object generating inferences   : 23
% 0.37/0.56  # Proof object simplifying inferences  : 66
% 0.37/0.56  # Training examples: 0 positive, 0 negative
% 0.37/0.56  # Parsed axioms                        : 9
% 0.37/0.56  # Removed by relevancy pruning/SinE    : 0
% 0.37/0.56  # Initial clauses                      : 35
% 0.37/0.56  # Removed in clause preprocessing      : 0
% 0.37/0.56  # Initial clauses in saturation        : 35
% 0.37/0.56  # Processed clauses                    : 536
% 0.37/0.56  # ...of these trivial                  : 0
% 0.37/0.56  # ...subsumed                          : 16
% 0.37/0.56  # ...remaining for further processing  : 520
% 0.37/0.56  # Other redundant clauses eliminated   : 0
% 0.37/0.56  # Clauses deleted for lack of memory   : 0
% 0.37/0.56  # Backward-subsumed                    : 1
% 0.37/0.56  # Backward-rewritten                   : 59
% 0.37/0.56  # Generated clauses                    : 4163
% 0.37/0.56  # ...of the previous two non-trivial   : 4162
% 0.37/0.56  # Contextual simplify-reflections      : 146
% 0.37/0.56  # Paramodulations                      : 4163
% 0.37/0.56  # Factorizations                       : 0
% 0.37/0.56  # Equation resolutions                 : 0
% 0.37/0.56  # Propositional unsat checks           : 0
% 0.37/0.56  #    Propositional check models        : 0
% 0.37/0.56  #    Propositional check unsatisfiable : 0
% 0.37/0.56  #    Propositional clauses             : 0
% 0.37/0.56  #    Propositional clauses after purity: 0
% 0.37/0.56  #    Propositional unsat core size     : 0
% 0.37/0.56  #    Propositional preprocessing time  : 0.000
% 0.37/0.56  #    Propositional encoding time       : 0.000
% 0.37/0.56  #    Propositional solver time         : 0.000
% 0.37/0.56  #    Success case prop preproc time    : 0.000
% 0.37/0.56  #    Success case prop encoding time   : 0.000
% 0.37/0.56  #    Success case prop solver time     : 0.000
% 0.37/0.56  # Current number of processed clauses  : 425
% 0.37/0.56  #    Positive orientable unit clauses  : 221
% 0.37/0.56  #    Positive unorientable unit clauses: 0
% 0.37/0.56  #    Negative unit clauses             : 4
% 0.37/0.56  #    Non-unit-clauses                  : 200
% 0.37/0.56  # Current number of unprocessed clauses: 3696
% 0.37/0.56  # ...number of literals in the above   : 9362
% 0.37/0.56  # Current number of archived formulas  : 0
% 0.37/0.56  # Current number of archived clauses   : 95
% 0.37/0.56  # Clause-clause subsumption calls (NU) : 13681
% 0.37/0.56  # Rec. Clause-clause subsumption calls : 8240
% 0.37/0.56  # Non-unit clause-clause subsumptions  : 163
% 0.37/0.56  # Unit Clause-clause subsumption calls : 228
% 0.37/0.56  # Rewrite failures with RHS unbound    : 0
% 0.37/0.56  # BW rewrite match attempts            : 11160
% 0.37/0.56  # BW rewrite match successes           : 4
% 0.37/0.56  # Condensation attempts                : 0
% 0.37/0.56  # Condensation successes               : 0
% 0.37/0.56  # Termbank termtop insertions          : 293888
% 0.39/0.56  
% 0.39/0.56  # -------------------------------------------------
% 0.39/0.56  # User time                : 0.209 s
% 0.39/0.56  # System time              : 0.011 s
% 0.39/0.56  # Total time               : 0.220 s
% 0.39/0.56  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
