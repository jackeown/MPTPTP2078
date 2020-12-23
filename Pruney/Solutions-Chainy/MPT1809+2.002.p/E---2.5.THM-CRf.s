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

% Result     : Theorem 0.85s
% Output     : CNFRefutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   74 (1047 expanded)
%              Number of clauses        :   57 ( 329 expanded)
%              Number of leaves         :    8 ( 251 expanded)
%              Depth                    :    9
%              Number of atoms          :  466 (16630 expanded)
%              Number of equality atoms :   39 (2093 expanded)
%              Maximal formula depth    :   32 (   7 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_tmap_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_tmap_1)).

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

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

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

fof(c_0_9,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ v1_funct_1(X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k2_partfun1(X17,X18,X19,X20) = k7_relat_1(X19,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_10,negated_conjecture,
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
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).

fof(c_0_11,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v2_struct_0(k1_tsep_1(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) )
      & ( v1_pre_topc(k1_tsep_1(X25,X26,X27))
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) )
      & ( m1_pre_topc(k1_tsep_1(X25,X26,X27),X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

fof(c_0_12,plain,(
    ! [X14,X15,X16] :
      ( ( v4_relat_1(X16,X14)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) )
      & ( v5_relat_1(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_13,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_14,plain,(
    ! [X28,X29,X30,X31,X32,X33,X34,X35] :
      ( ( r1_tmap_1(X31,X29,k2_tmap_1(X28,X29,X30,X31),X34)
        | ~ r1_tmap_1(k1_tsep_1(X28,X31,X32),X29,k2_tmap_1(X28,X29,X30,k1_tsep_1(X28,X31,X32)),X33)
        | X33 != X34
        | X33 != X35
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(k1_tsep_1(X28,X31,X32)))
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X28)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( r1_tmap_1(X32,X29,k2_tmap_1(X28,X29,X30,X32),X35)
        | ~ r1_tmap_1(k1_tsep_1(X28,X31,X32),X29,k2_tmap_1(X28,X29,X30,k1_tsep_1(X28,X31,X32)),X33)
        | X33 != X34
        | X33 != X35
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(k1_tsep_1(X28,X31,X32)))
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X28)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ r1_tmap_1(X31,X29,k2_tmap_1(X28,X29,X30,X31),X34)
        | ~ r1_tmap_1(X32,X29,k2_tmap_1(X28,X29,X30,X32),X35)
        | r1_tmap_1(k1_tsep_1(X28,X31,X32),X29,k2_tmap_1(X28,X29,X30,k1_tsep_1(X28,X31,X32)),X33)
        | X33 != X34
        | X33 != X35
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ m1_subset_1(X33,u1_struct_0(k1_tsep_1(X28,X31,X32)))
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X28)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).

fof(c_0_15,plain,(
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

cnf(c_0_16,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ v4_relat_1(X10,X9)
      | X10 = k7_relat_1(X10,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_25,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_26,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_29,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1) = k7_relat_1(esk3_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])]),c_0_22]),c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( esk1_0 = k1_tsep_1(esk1_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_17])).

cnf(c_0_43,plain,
    ( r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)
    | ~ r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).

cnf(c_0_44,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_47,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X5)
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X1,X6)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_49,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(X1)) = k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_21]),c_0_32]),c_0_33]),c_0_18]),c_0_17])]),c_0_34]),c_0_23]),c_0_35])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( k7_relat_1(esk3_0,u1_struct_0(esk1_0)) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_52,negated_conjecture,
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
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_30]),c_0_21]),c_0_31]),c_0_33]),c_0_32]),c_0_18]),c_0_17])]),c_0_34]),c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_56,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X6)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X5)
    | ~ m1_pre_topc(X6,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X6,X1)))
    | ~ m1_subset_1(X5,u1_struct_0(X6))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).

cnf(c_0_59,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(esk1_0,X1,X3),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X3)),X2)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X1,X3)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_30]),c_0_21]),c_0_31]),c_0_33]),c_0_32]),c_0_18]),c_0_17])]),c_0_34]),c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(k1_tsep_1(esk1_0,X1,esk5_0),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),esk6_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)))
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_20]),c_0_54])]),c_0_22])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(k1_tsep_1(esk1_0,X3,X1),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X3,X1)),X2)
    | ~ m1_pre_topc(X3,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X3,X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_30]),c_0_21]),c_0_31]),c_0_33]),c_0_32]),c_0_18]),c_0_17])]),c_0_34]),c_0_23])).

cnf(c_0_66,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)
    | ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_38]),c_0_60]),c_0_20]),c_0_37])]),c_0_22]),c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_38]),c_0_38]),c_0_60]),c_0_37]),c_0_38]),c_0_63]),c_0_64])]),c_0_39])).

cnf(c_0_69,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_38]),c_0_60]),c_0_37]),c_0_20])]),c_0_39]),c_0_22])).

cnf(c_0_70,negated_conjecture,
    ( ~ r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)
    | ~ r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_56]),c_0_45])).

cnf(c_0_71,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_63]),c_0_54]),c_0_64])])).

cnf(c_0_72,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_68]),c_0_63]),c_0_64]),c_0_54])])).

cnf(c_0_73,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_68])]),c_0_71]),c_0_72])]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.85/1.04  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.85/1.04  # and selection function SelectCQIPrecWNTNp.
% 0.85/1.04  #
% 0.85/1.04  # Preprocessing time       : 0.029 s
% 0.85/1.04  # Presaturation interreduction done
% 0.85/1.04  
% 0.85/1.04  # Proof found!
% 0.85/1.04  # SZS status Theorem
% 0.85/1.04  # SZS output start CNFRefutation
% 0.85/1.04  fof(t125_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 0.85/1.04  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.85/1.04  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.85/1.04  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.85/1.04  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.85/1.04  fof(t124_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>![X6]:(m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X4,X5)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(k1_tsep_1(X1,X4,X5),X2,k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_tmap_1)).
% 0.85/1.04  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.85/1.04  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 0.85/1.04  fof(c_0_8, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))))), inference(assume_negation,[status(cth)],[t125_tmap_1])).
% 0.85/1.04  fof(c_0_9, plain, ![X17, X18, X19, X20]:(~v1_funct_1(X19)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|k2_partfun1(X17,X18,X19,X20)=k7_relat_1(X19,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.85/1.04  fof(c_0_10, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk1_0))&(esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)&(m1_subset_1(esk6_0,u1_struct_0(esk1_0))&(m1_subset_1(esk7_0,u1_struct_0(esk4_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&((esk6_0=esk7_0&esk6_0=esk8_0)&((~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|(~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)))&((r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0))&(r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])])).
% 0.85/1.04  fof(c_0_11, plain, ![X25, X26, X27]:(((~v2_struct_0(k1_tsep_1(X25,X26,X27))|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25)))&(v1_pre_topc(k1_tsep_1(X25,X26,X27))|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25))))&(m1_pre_topc(k1_tsep_1(X25,X26,X27),X25)|(v2_struct_0(X25)|~l1_pre_topc(X25)|v2_struct_0(X26)|~m1_pre_topc(X26,X25)|v2_struct_0(X27)|~m1_pre_topc(X27,X25)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.85/1.04  fof(c_0_12, plain, ![X14, X15, X16]:((v4_relat_1(X16,X14)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))&(v5_relat_1(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.85/1.04  fof(c_0_13, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.85/1.04  fof(c_0_14, plain, ![X28, X29, X30, X31, X32, X33, X34, X35]:(((r1_tmap_1(X31,X29,k2_tmap_1(X28,X29,X30,X31),X34)|~r1_tmap_1(k1_tsep_1(X28,X31,X32),X29,k2_tmap_1(X28,X29,X30,k1_tsep_1(X28,X31,X32)),X33)|(X33!=X34|X33!=X35)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(k1_tsep_1(X28,X31,X32)))|(v2_struct_0(X32)|~m1_pre_topc(X32,X28))|(v2_struct_0(X31)|~m1_pre_topc(X31,X28))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(r1_tmap_1(X32,X29,k2_tmap_1(X28,X29,X30,X32),X35)|~r1_tmap_1(k1_tsep_1(X28,X31,X32),X29,k2_tmap_1(X28,X29,X30,k1_tsep_1(X28,X31,X32)),X33)|(X33!=X34|X33!=X35)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(k1_tsep_1(X28,X31,X32)))|(v2_struct_0(X32)|~m1_pre_topc(X32,X28))|(v2_struct_0(X31)|~m1_pre_topc(X31,X28))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28))))&(~r1_tmap_1(X31,X29,k2_tmap_1(X28,X29,X30,X31),X34)|~r1_tmap_1(X32,X29,k2_tmap_1(X28,X29,X30,X32),X35)|r1_tmap_1(k1_tsep_1(X28,X31,X32),X29,k2_tmap_1(X28,X29,X30,k1_tsep_1(X28,X31,X32)),X33)|(X33!=X34|X33!=X35)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X31))|~m1_subset_1(X33,u1_struct_0(k1_tsep_1(X28,X31,X32)))|(v2_struct_0(X32)|~m1_pre_topc(X32,X28))|(v2_struct_0(X31)|~m1_pre_topc(X31,X28))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).
% 0.85/1.04  fof(c_0_15, plain, ![X21, X22, X23, X24]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_pre_topc(X24,X21)|k2_tmap_1(X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.85/1.04  cnf(c_0_16, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.85/1.04  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_19, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.85/1.04  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk5_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_22, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  fof(c_0_24, plain, ![X9, X10]:(~v1_relat_1(X10)|~v4_relat_1(X10,X9)|X10=k7_relat_1(X10,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.85/1.04  cnf(c_0_25, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.85/1.04  cnf(c_0_26, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.85/1.04  cnf(c_0_27, plain, (r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X8)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tmap_1(X6,X2,k2_tmap_1(X3,X2,X4,X6),X7)|X8!=X5|X8!=X7|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.85/1.04  cnf(c_0_28, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X7)|X7!=X5|X7!=X8|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.85/1.04  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.85/1.04  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_35, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,X1)=k7_relat_1(esk3_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18])])).
% 0.85/1.04  cnf(c_0_36, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk1_0,X1,esk5_0),esk1_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])]), c_0_22]), c_0_23])).
% 0.85/1.04  cnf(c_0_37, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_38, negated_conjecture, (esk1_0=k1_tsep_1(esk1_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_40, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.85/1.04  cnf(c_0_41, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_25, c_0_17])).
% 0.85/1.04  cnf(c_0_42, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_26, c_0_17])).
% 0.85/1.04  cnf(c_0_43, plain, (r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)|~r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))|~l1_pre_topc(X1)|~l1_pre_topc(X4)|~v2_pre_topc(X1)|~v2_pre_topc(X4)|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X6,u1_struct_0(X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_27])])).
% 0.85/1.04  cnf(c_0_44, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_45, negated_conjecture, (esk6_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_47, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X6)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X7)|X7!=X8|X7!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(k1_tsep_1(X3,X6,X1)))|~m1_pre_topc(X1,X3)|~m1_pre_topc(X6,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.85/1.04  cnf(c_0_48, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X5)|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_subset_1(X5,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 0.85/1.04  cnf(c_0_49, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(X1))=k2_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_pre_topc(X1,esk1_0)), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), c_0_21]), c_0_32]), c_0_33]), c_0_18]), c_0_17])]), c_0_34]), c_0_23]), c_0_35])).
% 0.85/1.04  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_39])).
% 0.85/1.04  cnf(c_0_51, negated_conjecture, (k7_relat_1(esk3_0,u1_struct_0(esk1_0))=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.85/1.04  cnf(c_0_52, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk1_0,X1,X2),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X2)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(X2,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X2),X3)|~r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X3)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(X3,u1_struct_0(k1_tsep_1(esk1_0,X1,X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_30]), c_0_21]), c_0_31]), c_0_33]), c_0_32]), c_0_18]), c_0_17])]), c_0_34]), c_0_23])).
% 0.85/1.04  cnf(c_0_53, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_44, c_0_45])).
% 0.85/1.04  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_46, c_0_45])).
% 0.85/1.04  cnf(c_0_55, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_56, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_58, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X6)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(X3,X6,X1),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X6,X1)),X5)|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(k1_tsep_1(X3,X6,X1)))|~m1_subset_1(X5,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_47])])).
% 0.85/1.04  cnf(c_0_59, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)|v2_struct_0(X3)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(esk1_0,X1,X3),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,X3)),X2)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X1,X3)))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_30]), c_0_21]), c_0_31]), c_0_33]), c_0_32]), c_0_18]), c_0_17])]), c_0_34]), c_0_23])).
% 0.85/1.04  cnf(c_0_60, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk3_0,esk1_0)=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])).
% 0.85/1.04  cnf(c_0_61, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk1_0,X1,esk5_0),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X1,esk5_0)),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|v2_struct_0(X1)|~r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),esk6_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(esk6_0,u1_struct_0(k1_tsep_1(esk1_0,X1,esk5_0)))|~m1_subset_1(esk6_0,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_20]), c_0_54])]), c_0_22])).
% 0.85/1.04  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[c_0_55, c_0_56])).
% 0.85/1.04  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_57, c_0_56])).
% 0.85/1.04  cnf(c_0_65, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,X1),X2)|v2_struct_0(X3)|v2_struct_0(X1)|~r1_tmap_1(k1_tsep_1(esk1_0,X3,X1),esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,k1_tsep_1(esk1_0,X3,X1)),X2)|~m1_pre_topc(X3,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk1_0,X3,X1)))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_30]), c_0_21]), c_0_31]), c_0_33]), c_0_32]), c_0_18]), c_0_17])]), c_0_34]), c_0_23])).
% 0.85/1.04  cnf(c_0_66, negated_conjecture, (~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)|~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk7_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.85/1.04  cnf(c_0_67, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_38]), c_0_60]), c_0_20]), c_0_37])]), c_0_22]), c_0_39])).
% 0.85/1.04  cnf(c_0_68, negated_conjecture, (r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_38]), c_0_38]), c_0_60]), c_0_37]), c_0_38]), c_0_63]), c_0_64])]), c_0_39])).
% 0.85/1.04  cnf(c_0_69, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),X1)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,X1)|~m1_subset_1(X1,u1_struct_0(esk1_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_38]), c_0_60]), c_0_37]), c_0_20])]), c_0_39]), c_0_22])).
% 0.85/1.04  cnf(c_0_70, negated_conjecture, (~r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)|~r1_tmap_1(esk1_0,esk2_0,esk3_0,esk6_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_56]), c_0_45])).
% 0.85/1.04  cnf(c_0_71, negated_conjecture, (r1_tmap_1(esk4_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk4_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_63]), c_0_54]), c_0_64])])).
% 0.85/1.04  cnf(c_0_72, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk1_0,esk2_0,esk3_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_68]), c_0_63]), c_0_64]), c_0_54])])).
% 0.85/1.04  cnf(c_0_73, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_68])]), c_0_71]), c_0_72])]), ['proof']).
% 0.85/1.04  # SZS output end CNFRefutation
% 0.85/1.04  # Proof object total steps             : 74
% 0.85/1.04  # Proof object clause steps            : 57
% 0.85/1.04  # Proof object formula steps           : 17
% 0.85/1.04  # Proof object conjectures             : 48
% 0.85/1.04  # Proof object clause conjectures      : 45
% 0.85/1.04  # Proof object formula conjectures     : 3
% 0.85/1.04  # Proof object initial clauses used    : 31
% 0.85/1.04  # Proof object initial formulas used   : 8
% 0.85/1.04  # Proof object generating inferences   : 17
% 0.85/1.04  # Proof object simplifying inferences  : 98
% 0.85/1.04  # Training examples: 0 positive, 0 negative
% 0.85/1.04  # Parsed axioms                        : 8
% 0.85/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.85/1.04  # Initial clauses                      : 34
% 0.85/1.04  # Removed in clause preprocessing      : 0
% 0.85/1.04  # Initial clauses in saturation        : 34
% 0.85/1.04  # Processed clauses                    : 2888
% 0.85/1.04  # ...of these trivial                  : 0
% 0.85/1.04  # ...subsumed                          : 3
% 0.85/1.04  # ...remaining for further processing  : 2884
% 0.85/1.04  # Other redundant clauses eliminated   : 6
% 0.85/1.04  # Clauses deleted for lack of memory   : 0
% 0.85/1.04  # Backward-subsumed                    : 0
% 0.85/1.04  # Backward-rewritten                   : 4
% 0.85/1.04  # Generated clauses                    : 86417
% 0.85/1.04  # ...of the previous two non-trivial   : 86417
% 0.85/1.04  # Contextual simplify-reflections      : 0
% 0.85/1.04  # Paramodulations                      : 86414
% 0.85/1.04  # Factorizations                       : 0
% 0.85/1.04  # Equation resolutions                 : 6
% 0.85/1.04  # Propositional unsat checks           : 0
% 0.85/1.04  #    Propositional check models        : 0
% 0.85/1.04  #    Propositional check unsatisfiable : 0
% 0.85/1.04  #    Propositional clauses             : 0
% 0.85/1.04  #    Propositional clauses after purity: 0
% 0.85/1.04  #    Propositional unsat core size     : 0
% 0.85/1.04  #    Propositional preprocessing time  : 0.000
% 0.85/1.04  #    Propositional encoding time       : 0.000
% 0.85/1.04  #    Propositional solver time         : 0.000
% 0.85/1.04  #    Success case prop preproc time    : 0.000
% 0.85/1.04  #    Success case prop encoding time   : 0.000
% 0.85/1.04  #    Success case prop solver time     : 0.000
% 0.85/1.04  # Current number of processed clauses  : 2843
% 0.85/1.04  #    Positive orientable unit clauses  : 699
% 0.85/1.04  #    Positive unorientable unit clauses: 0
% 0.85/1.04  #    Negative unit clauses             : 1864
% 0.85/1.04  #    Non-unit-clauses                  : 280
% 0.85/1.04  # Current number of unprocessed clauses: 83597
% 0.85/1.04  # ...number of literals in the above   : 87127
% 0.85/1.04  # Current number of archived formulas  : 0
% 0.85/1.04  # Current number of archived clauses   : 38
% 0.85/1.04  # Clause-clause subsumption calls (NU) : 25498
% 0.85/1.04  # Rec. Clause-clause subsumption calls : 22920
% 0.85/1.04  # Non-unit clause-clause subsumptions  : 2
% 0.85/1.04  # Unit Clause-clause subsumption calls : 364072
% 0.85/1.04  # Rewrite failures with RHS unbound    : 0
% 0.85/1.04  # BW rewrite match attempts            : 82216
% 0.85/1.04  # BW rewrite match successes           : 1
% 0.85/1.04  # Condensation attempts                : 0
% 0.85/1.04  # Condensation successes               : 0
% 0.85/1.04  # Termbank termtop insertions          : 3155135
% 0.85/1.05  
% 0.85/1.05  # -------------------------------------------------
% 0.85/1.05  # User time                : 0.666 s
% 0.85/1.05  # System time              : 0.043 s
% 0.85/1.05  # Total time               : 0.708 s
% 0.85/1.05  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
