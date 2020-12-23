%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:30 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   82 (1139 expanded)
%              Number of clauses        :   61 ( 364 expanded)
%              Number of leaves         :   10 ( 274 expanded)
%              Depth                    :   10
%              Number of atoms          :  497 (17549 expanded)
%              Number of equality atoms :   39 (2192 expanded)
%              Maximal formula depth    :   32 (   6 average)
%              Maximal clause size      :   61 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t125_tmap_1,conjecture,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ( X1 = k1_tsep_1(X1,X4,X5)
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X5))
                                   => ( ( X6 = X7
                                        & X6 = X8 )
                                     => ( r1_tmap_1(X1,X2,X3,X6)
                                      <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                          & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_tmap_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t124_tmap_1,axiom,(
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
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( ~ v2_struct_0(X5)
                        & m1_pre_topc(X5,X1) )
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X4,X5)))
                         => ! [X7] :
                              ( m1_subset_1(X7,u1_struct_0(X4))
                             => ! [X8] :
                                  ( m1_subset_1(X8,u1_struct_0(X5))
                                 => ( ( X6 = X7
                                      & X6 = X8 )
                                   => ( r1_tmap_1(k1_tsep_1(X1,X4,X5),X2,k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),X6)
                                    <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                        & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_tmap_1)).

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

fof(t97_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X1)
       => k7_relat_1(X2,X1) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(c_0_10,negated_conjecture,(
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
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( ~ v2_struct_0(X5)
                          & m1_pre_topc(X5,X1) )
                       => ( X1 = k1_tsep_1(X1,X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ! [X8] :
                                      ( m1_subset_1(X8,u1_struct_0(X5))
                                     => ( ( X6 = X7
                                          & X6 = X8 )
                                       => ( r1_tmap_1(X1,X2,X3,X6)
                                        <=> ( r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)
                                            & r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t125_tmap_1])).

fof(c_0_11,plain,(
    ! [X16,X17,X18] :
      ( ( v4_relat_1(X18,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( v5_relat_1(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk1_0)
    & esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & esk6_0 = esk7_0
    & esk6_0 = esk8_0
    & ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
      | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
      | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) )
    & ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
      | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) )
    & ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
      | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | v1_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X19,X20,X21,X22] :
      ( ~ v1_funct_1(X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_partfun1(X19,X20,X21,X22) = k7_relat_1(X21,X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_15,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_struct_0(k1_tsep_1(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30) )
      & ( v1_pre_topc(k1_tsep_1(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30) )
      & ( m1_pre_topc(k1_tsep_1(X30,X31,X32),X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_16,plain,(
    ! [X9,X10] :
      ( ( ~ v4_relat_1(X10,X9)
        | r1_tarski(k1_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k1_relat_1(X10),X9)
        | v4_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_17,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X33,X34,X35,X36,X37,X38,X39,X40] :
      ( ( r1_tmap_1(X36,X34,k2_tmap_1(X33,X34,X35,X36),X39)
        | ~ r1_tmap_1(k1_tsep_1(X33,X36,X37),X34,k2_tmap_1(X33,X34,X35,k1_tsep_1(X33,X36,X37)),X38)
        | X38 != X39
        | X38 != X40
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(k1_tsep_1(X33,X36,X37)))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X33)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( r1_tmap_1(X37,X34,k2_tmap_1(X33,X34,X35,X37),X40)
        | ~ r1_tmap_1(k1_tsep_1(X33,X36,X37),X34,k2_tmap_1(X33,X34,X35,k1_tsep_1(X33,X36,X37)),X38)
        | X38 != X39
        | X38 != X40
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(k1_tsep_1(X33,X36,X37)))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X33)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r1_tmap_1(X36,X34,k2_tmap_1(X33,X34,X35,X36),X39)
        | ~ r1_tmap_1(X37,X34,k2_tmap_1(X33,X34,X35,X37),X40)
        | r1_tmap_1(k1_tsep_1(X33,X36,X37),X34,k2_tmap_1(X33,X34,X35,k1_tsep_1(X33,X36,X37)),X38)
        | X38 != X39
        | X38 != X40
        | ~ m1_subset_1(X40,u1_struct_0(X37))
        | ~ m1_subset_1(X39,u1_struct_0(X36))
        | ~ m1_subset_1(X38,u1_struct_0(k1_tsep_1(X33,X36,X37)))
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X33)
        | v2_struct_0(X36)
        | ~ m1_pre_topc(X36,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
        | v2_struct_0(X34)
        | ~ v2_pre_topc(X34)
        | ~ l1_pre_topc(X34)
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).

fof(c_0_21,plain,(
    ! [X26,X27,X28,X29] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))
      | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))
      | ~ m1_pre_topc(X29,X26)
      | k2_tmap_1(X26,X27,X28,X29) = k2_partfun1(u1_struct_0(X26),u1_struct_0(X27),X28,u1_struct_0(X29)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_22,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_29,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(k1_relat_1(X12),X11)
      | k7_relat_1(X12,X11) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_33,plain,
    ( r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X8)
    | v2_struct_0(X6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | ~ r1_tmap_1(X6,X2,k2_tmap_1(X3,X2,X4,X6),X7)
    | X8 != X5
    | X8 != X7
    | ~ m1_subset_1(X7,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X7)
    | X7 != X5
    | X7 != X8
    | ~ m1_subset_1(X8,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_37,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_23])])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( k7_relat_1(X1,X2) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk3_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

fof(c_0_48,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ l1_pre_topc(X23)
      | v2_struct_0(X24)
      | ~ m1_pre_topc(X24,X23)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | m1_subset_1(X25,u1_struct_0(X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_49,plain,
    ( r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)
    | ~ r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).

cnf(c_0_50,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( esk6_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X6)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X7)
    | X7 != X8
    | X7 != X5
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ m1_subset_1(X8,u1_struct_0(X6))
    | ~ m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X6,X1)))
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X6,X3)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_55,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39]),c_0_40]),c_0_26]),c_0_23]),c_0_18])]),c_0_41]),c_0_28])).

cnf(c_0_56,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44]),c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(esk1_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_32])])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(k1_tsep_1(esk1_0,X1,X2),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X2)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X2,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X2),X3)
    | ~ r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X3)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(esk1_0,X1,X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_36]),c_0_39]),c_0_38]),c_0_26]),c_0_40]),c_0_23]),c_0_18])]),c_0_41]),c_0_28])).

cnf(c_0_60,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_52,c_0_51])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_63,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_65,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X6,X1)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(esk1_0,X1,X3),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X3)),X2)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X1,X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_36]),c_0_39]),c_0_38]),c_0_26]),c_0_40]),c_0_23]),c_0_18])]),c_0_41]),c_0_28])).

cnf(c_0_67,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( r1_tmap_1(k1_tsep_1(esk1_0,X1,esk5_0),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),esk6_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_25]),c_0_61])]),c_0_27])).

cnf(c_0_70,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(esk1_0,X3,X1),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X3,X1)),X2)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X3,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_36]),c_0_39]),c_0_38]),c_0_26]),c_0_40]),c_0_23]),c_0_18])]),c_0_41]),c_0_28])).

cnf(c_0_74,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_75,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_44]),c_0_67]),c_0_25]),c_0_43])]),c_0_27]),c_0_45]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_44]),c_0_44]),c_0_67]),c_0_43]),c_0_44]),c_0_71]),c_0_72])]),c_0_45])).

cnf(c_0_77,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_44]),c_0_67]),c_0_43]),c_0_25])]),c_0_45]),c_0_27]),c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_63]),c_0_51])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_61]),c_0_72])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_76]),c_0_72]),c_0_61])])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_76])]),c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 1.61/1.77  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 1.61/1.77  # and selection function SelectCQIPrecWNTNp.
% 1.61/1.77  #
% 1.61/1.77  # Preprocessing time       : 0.029 s
% 1.61/1.77  # Presaturation interreduction done
% 1.61/1.77  
% 1.61/1.77  # Proof found!
% 1.61/1.77  # SZS status Theorem
% 1.61/1.77  # SZS output start CNFRefutation
% 1.61/1.77  fof(t125_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_tmap_1)).
% 1.61/1.77  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.61/1.77  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.61/1.77  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 1.61/1.77  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 1.61/1.77  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.61/1.77  fof(t124_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>![X6]:(m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X4,X5)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(k1_tsep_1(X1,X4,X5),X2,k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_tmap_1)).
% 1.61/1.77  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 1.61/1.77  fof(t97_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X2),X1)=>k7_relat_1(X2,X1)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.61/1.77  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 1.61/1.77  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))))), inference(assume_negation,[status(cth)],[t125_tmap_1])).
% 1.61/1.77  fof(c_0_11, plain, ![X16, X17, X18]:((v4_relat_1(X18,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))&(v5_relat_1(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.61/1.77  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk1_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((esk6_0=esk7_0&esk6_0=esk8_0)&((~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|(~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)))&((r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0))&(r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).
% 1.61/1.77  fof(c_0_13, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|v1_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.61/1.77  fof(c_0_14, plain, ![X19, X20, X21, X22]:(~v1_funct_1(X21)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_partfun1(X19,X20,X21,X22)=k7_relat_1(X21,X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 1.61/1.77  fof(c_0_15, plain, ![X30, X31, X32]:(((~v2_struct_0(k1_tsep_1(X30,X31,X32))|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)))&(v1_pre_topc(k1_tsep_1(X30,X31,X32))|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30))))&(m1_pre_topc(k1_tsep_1(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 1.61/1.77  fof(c_0_16, plain, ![X9, X10]:((~v4_relat_1(X10,X9)|r1_tarski(k1_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k1_relat_1(X10),X9)|v4_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.61/1.77  cnf(c_0_17, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.61/1.77  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_19, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.61/1.77  fof(c_0_20, plain, ![X33, X34, X35, X36, X37, X38, X39, X40]:(((r1_tmap_1(X36,X34,k2_tmap_1(X33,X34,X35,X36),X39)|~r1_tmap_1(k1_tsep_1(X33,X36,X37),X34,k2_tmap_1(X33,X34,X35,k1_tsep_1(X33,X36,X37)),X38)|(X38!=X39|X38!=X40)|~m1_subset_1(X40,u1_struct_0(X37))|~m1_subset_1(X39,u1_struct_0(X36))|~m1_subset_1(X38,u1_struct_0(k1_tsep_1(X33,X36,X37)))|(v2_struct_0(X37)|~m1_pre_topc(X37,X33))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34)))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(r1_tmap_1(X37,X34,k2_tmap_1(X33,X34,X35,X37),X40)|~r1_tmap_1(k1_tsep_1(X33,X36,X37),X34,k2_tmap_1(X33,X34,X35,k1_tsep_1(X33,X36,X37)),X38)|(X38!=X39|X38!=X40)|~m1_subset_1(X40,u1_struct_0(X37))|~m1_subset_1(X39,u1_struct_0(X36))|~m1_subset_1(X38,u1_struct_0(k1_tsep_1(X33,X36,X37)))|(v2_struct_0(X37)|~m1_pre_topc(X37,X33))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34)))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33))))&(~r1_tmap_1(X36,X34,k2_tmap_1(X33,X34,X35,X36),X39)|~r1_tmap_1(X37,X34,k2_tmap_1(X33,X34,X35,X37),X40)|r1_tmap_1(k1_tsep_1(X33,X36,X37),X34,k2_tmap_1(X33,X34,X35,k1_tsep_1(X33,X36,X37)),X38)|(X38!=X39|X38!=X40)|~m1_subset_1(X40,u1_struct_0(X37))|~m1_subset_1(X39,u1_struct_0(X36))|~m1_subset_1(X38,u1_struct_0(k1_tsep_1(X33,X36,X37)))|(v2_struct_0(X37)|~m1_pre_topc(X37,X33))|(v2_struct_0(X36)|~m1_pre_topc(X36,X33))|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34)))))|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).
% 1.61/1.77  fof(c_0_21, plain, ![X26, X27, X28, X29]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|(~m1_pre_topc(X29,X26)|k2_tmap_1(X26,X27,X28,X29)=k2_partfun1(u1_struct_0(X26),u1_struct_0(X27),X28,u1_struct_0(X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 1.61/1.77  cnf(c_0_22, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.61/1.77  cnf(c_0_23, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_24, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.61/1.77  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  fof(c_0_29, plain, ![X11, X12]:(~v1_relat_1(X12)|(~r1_tarski(k1_relat_1(X12),X11)|k7_relat_1(X12,X11)=X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t97_relat_1])])).
% 1.61/1.77  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.61/1.77  cnf(c_0_31, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 1.61/1.77  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 1.61/1.77  cnf(c_0_33, plain, (r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X8)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tmap_1(X6,X2,k2_tmap_1(X3,X2,X4,X6),X7)|X8!=X5|X8!=X7|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.61/1.77  cnf(c_0_34, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X7)|X7!=X5|X7!=X8|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.61/1.77  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.61/1.77  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_37, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_23])])).
% 1.61/1.77  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_39, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_40, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_41, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_42, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 1.61/1.77  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_44, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_45, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_46, plain, (k7_relat_1(X1,X2)=X1|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.61/1.77  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(esk3_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 1.61/1.77  fof(c_0_48, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~l1_pre_topc(X23)|(v2_struct_0(X24)|~m1_pre_topc(X24,X23)|(~m1_subset_1(X25,u1_struct_0(X24))|m1_subset_1(X25,u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 1.61/1.77  cnf(c_0_49, plain, (r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)|~r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))|~v2_pre_topc(X1)|~v2_pre_topc(X4)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X4)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X6,u1_struct_0(X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_33])])).
% 1.61/1.77  cnf(c_0_50, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_51, negated_conjecture, (esk6_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_53, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X6)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X7)|X7!=X8|X7!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X6,X1)))|~m1_pre_topc(X1,X3)|~m1_pre_topc(X6,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.61/1.77  cnf(c_0_54, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_subset_1(X5,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 1.61/1.77  cnf(c_0_55, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39]), c_0_40]), c_0_26]), c_0_23]), c_0_18])]), c_0_41]), c_0_28])).
% 1.61/1.77  cnf(c_0_56, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44]), c_0_45])).
% 1.61/1.77  cnf(c_0_57, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(esk1_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_32])])).
% 1.61/1.77  cnf(c_0_58, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 1.61/1.77  cnf(c_0_59, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk1_0,X1,X2),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X2)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(X2,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X2),X3)|~r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X3)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(X3,u1_struct_0(k1_tsep_1(esk1_0,X1,X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_36]), c_0_39]), c_0_38]), c_0_26]), c_0_40]), c_0_23]), c_0_18])]), c_0_41]), c_0_28])).
% 1.61/1.77  cnf(c_0_60, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_50, c_0_51])).
% 1.61/1.77  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_52, c_0_51])).
% 1.61/1.77  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_63, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_65, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X6,X1)))|~m1_subset_1(X5,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_53])])).
% 1.61/1.77  cnf(c_0_66, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)|v2_struct_0(X3)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(esk1_0,X1,X3),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X3)),X2)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X1,X3)))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_36]), c_0_39]), c_0_38]), c_0_26]), c_0_40]), c_0_23]), c_0_18])]), c_0_41]), c_0_28])).
% 1.61/1.77  cnf(c_0_67, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 1.61/1.77  cnf(c_0_68, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 1.61/1.77  cnf(c_0_69, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk1_0,X1,esk5_0),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|v2_struct_0(X1)|~r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),esk6_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)))|~m1_subset_1(esk6_0,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_25]), c_0_61])]), c_0_27])).
% 1.61/1.77  cnf(c_0_70, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_62, c_0_63])).
% 1.61/1.77  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_64, c_0_63])).
% 1.61/1.77  cnf(c_0_73, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)|v2_struct_0(X3)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(esk1_0,X3,X1),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X3,X1)),X2)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X3,X1)))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_36]), c_0_39]), c_0_38]), c_0_26]), c_0_40]), c_0_23]), c_0_18])]), c_0_41]), c_0_28])).
% 1.61/1.77  cnf(c_0_74, negated_conjecture, (~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.61/1.77  cnf(c_0_75, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_44]), c_0_67]), c_0_25]), c_0_43])]), c_0_27]), c_0_45]), c_0_68])).
% 1.61/1.77  cnf(c_0_76, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_44]), c_0_44]), c_0_67]), c_0_43]), c_0_44]), c_0_71]), c_0_72])]), c_0_45])).
% 1.61/1.77  cnf(c_0_77, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_44]), c_0_67]), c_0_43]), c_0_25])]), c_0_45]), c_0_27]), c_0_68])).
% 1.61/1.77  cnf(c_0_78, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_63]), c_0_51])).
% 1.61/1.77  cnf(c_0_79, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_61]), c_0_72])])).
% 1.61/1.77  cnf(c_0_80, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_76]), c_0_72]), c_0_61])])).
% 1.61/1.77  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_76])]), c_0_79]), c_0_80])]), ['proof']).
% 1.61/1.77  # SZS output end CNFRefutation
% 1.61/1.77  # Proof object total steps             : 82
% 1.61/1.77  # Proof object clause steps            : 61
% 1.61/1.77  # Proof object formula steps           : 21
% 1.61/1.77  # Proof object conjectures             : 50
% 1.61/1.77  # Proof object clause conjectures      : 47
% 1.61/1.77  # Proof object formula conjectures     : 3
% 1.61/1.77  # Proof object initial clauses used    : 33
% 1.61/1.77  # Proof object initial formulas used   : 10
% 1.61/1.77  # Proof object generating inferences   : 19
% 1.61/1.77  # Proof object simplifying inferences  : 104
% 1.61/1.77  # Training examples: 0 positive, 0 negative
% 1.61/1.77  # Parsed axioms                        : 10
% 1.61/1.77  # Removed by relevancy pruning/SinE    : 0
% 1.61/1.77  # Initial clauses                      : 37
% 1.61/1.77  # Removed in clause preprocessing      : 0
% 1.61/1.77  # Initial clauses in saturation        : 37
% 1.61/1.77  # Processed clauses                    : 3933
% 1.61/1.77  # ...of these trivial                  : 0
% 1.61/1.77  # ...subsumed                          : 3
% 1.61/1.77  # ...remaining for further processing  : 3929
% 1.61/1.77  # Other redundant clauses eliminated   : 6
% 1.61/1.77  # Clauses deleted for lack of memory   : 0
% 1.61/1.77  # Backward-subsumed                    : 0
% 1.61/1.77  # Backward-rewritten                   : 4
% 1.61/1.77  # Generated clauses                    : 157061
% 1.61/1.77  # ...of the previous two non-trivial   : 157057
% 1.61/1.77  # Contextual simplify-reflections      : 2
% 1.61/1.77  # Paramodulations                      : 157058
% 1.61/1.77  # Factorizations                       : 0
% 1.61/1.77  # Equation resolutions                 : 6
% 1.61/1.77  # Propositional unsat checks           : 0
% 1.61/1.77  #    Propositional check models        : 0
% 1.61/1.77  #    Propositional check unsatisfiable : 0
% 1.61/1.77  #    Propositional clauses             : 0
% 1.61/1.77  #    Propositional clauses after purity: 0
% 1.61/1.77  #    Propositional unsat core size     : 0
% 1.61/1.77  #    Propositional preprocessing time  : 0.000
% 1.61/1.77  #    Propositional encoding time       : 0.000
% 1.61/1.77  #    Propositional solver time         : 0.000
% 1.61/1.77  #    Success case prop preproc time    : 0.000
% 1.61/1.77  #    Success case prop encoding time   : 0.000
% 1.61/1.77  #    Success case prop solver time     : 0.000
% 1.61/1.77  # Current number of processed clauses  : 3885
% 1.61/1.77  #    Positive orientable unit clauses  : 872
% 1.61/1.77  #    Positive unorientable unit clauses: 0
% 1.61/1.77  #    Negative unit clauses             : 2554
% 1.61/1.77  #    Non-unit-clauses                  : 459
% 1.61/1.77  # Current number of unprocessed clauses: 153198
% 1.61/1.77  # ...number of literals in the above   : 161527
% 1.61/1.77  # Current number of archived formulas  : 0
% 1.61/1.77  # Current number of archived clauses   : 41
% 1.61/1.77  # Clause-clause subsumption calls (NU) : 54118
% 1.61/1.77  # Rec. Clause-clause subsumption calls : 49377
% 1.61/1.77  # Non-unit clause-clause subsumptions  : 4
% 1.61/1.77  # Unit Clause-clause subsumption calls : 779577
% 1.61/1.77  # Rewrite failures with RHS unbound    : 0
% 1.61/1.77  # BW rewrite match attempts            : 100078
% 1.61/1.77  # BW rewrite match successes           : 1
% 1.61/1.77  # Condensation attempts                : 0
% 1.61/1.77  # Condensation successes               : 0
% 1.61/1.77  # Termbank termtop insertions          : 5864491
% 1.63/1.78  
% 1.63/1.78  # -------------------------------------------------
% 1.63/1.78  # User time                : 1.354 s
% 1.63/1.78  # System time              : 0.079 s
% 1.63/1.78  # Total time               : 1.432 s
% 1.63/1.78  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
