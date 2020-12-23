%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1760+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tmap_1)).

fof(redefinition_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k1_partfun1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_2)).

fof(dt_k1_partfun1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( v1_funct_1(X5)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( v1_funct_1(k1_partfun1(X1,X2,X3,X4,X5,X6))
        & m1_subset_1(k1_partfun1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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
    ! [X26,X27,X28,X29,X30,X31] :
      ( ~ v1_funct_1(X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | ~ v1_funct_1(X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | k1_partfun1(X26,X27,X28,X29,X30,X31) = k5_relat_1(X30,X31) ) ),
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
    ! [X21,X22,X23,X24,X25] :
      ( ( v1_funct_1(k5_relat_1(X24,X25))
        | v1_xboole_0(X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( v1_funct_2(k5_relat_1(X24,X25),X21,X23)
        | v1_xboole_0(X22)
        | ~ v1_funct_1(X24)
        | ~ v1_funct_2(X24,X21,X22)
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X22,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
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
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
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
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
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
    ! [X13,X14,X15,X16] :
      ( ( v1_funct_1(k2_tmap_1(X13,X14,X15,X16))
        | ~ l1_struct_0(X13)
        | ~ l1_struct_0(X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_struct_0(X16) )
      & ( v1_funct_2(k2_tmap_1(X13,X14,X15,X16),u1_struct_0(X16),u1_struct_0(X14))
        | ~ l1_struct_0(X13)
        | ~ l1_struct_0(X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_struct_0(X16) )
      & ( m1_subset_1(k2_tmap_1(X13,X14,X15,X16),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X14))))
        | ~ l1_struct_0(X13)
        | ~ l1_struct_0(X14)
        | ~ v1_funct_1(X15)
        | ~ v1_funct_2(X15,u1_struct_0(X13),u1_struct_0(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X13),u1_struct_0(X14))))
        | ~ l1_struct_0(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_2(k5_relat_1(X1,esk5_0),X2,u1_struct_0(esk3_0))
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
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_2(k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0)) ),
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
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_funct_2(k2_tmap_1(esk1_0,esk3_0,k1_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk6_0,esk5_0),X1),u1_struct_0(X1),u1_struct_0(esk3_0))
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
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
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
