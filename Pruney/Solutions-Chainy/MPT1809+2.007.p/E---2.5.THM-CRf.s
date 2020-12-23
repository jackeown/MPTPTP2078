%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 912 expanded)
%              Number of clauses        :   57 ( 289 expanded)
%              Number of leaves         :    9 ( 219 expanded)
%              Depth                    :   12
%              Number of atoms          :  517 (14505 expanded)
%              Number of equality atoms :   29 (1738 expanded)
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

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

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

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t64_tmap_1,axiom,(
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
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

fof(c_0_10,plain,(
    ! [X17,X18] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | m1_connsp_2(esk1_2(X17,X18),X17,X18) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

fof(c_0_11,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk2_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk2_0)
    & esk2_0 = k1_tsep_1(esk2_0,esk5_0,esk6_0)
    & m1_subset_1(esk7_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk6_0))
    & esk7_0 = esk8_0
    & esk7_0 = esk9_0
    & ( ~ r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)
      | ~ r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)
      | ~ r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0) )
    & ( r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)
      | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) )
    & ( r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0)
      | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).

fof(c_0_12,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] :
      ( ( ~ r1_tmap_1(X36,X35,X37,X40)
        | r1_tmap_1(X38,X35,k2_tmap_1(X36,X35,X37,X38),X41)
        | ~ r1_tarski(X39,u1_struct_0(X38))
        | ~ m1_connsp_2(X39,X36,X40)
        | X40 != X41
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X38)
        | ~ m1_pre_topc(X38,X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r1_tmap_1(X38,X35,k2_tmap_1(X36,X35,X37,X38),X41)
        | r1_tmap_1(X36,X35,X37,X40)
        | ~ r1_tarski(X39,u1_struct_0(X38))
        | ~ m1_connsp_2(X39,X36,X40)
        | X40 != X41
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X36)))
        | v2_struct_0(X38)
        | ~ m1_pre_topc(X38,X36)
        | ~ v1_funct_1(X37)
        | ~ v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X35))
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35))))
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,u1_struct_0(X14))
      | ~ m1_connsp_2(X16,X14,X15)
      | m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_14,plain,(
    ! [X11,X12,X13] :
      ( v2_struct_0(X11)
      | ~ l1_pre_topc(X11)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X12,X11)
      | ~ m1_subset_1(X13,u1_struct_0(X12))
      | m1_subset_1(X13,u1_struct_0(X11)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk1_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X20,X21,X22,X23,X24,X25,X26,X27] :
      ( ( r1_tmap_1(X23,X21,k2_tmap_1(X20,X21,X22,X23),X26)
        | ~ r1_tmap_1(k1_tsep_1(X20,X23,X24),X21,k2_tmap_1(X20,X21,X22,k1_tsep_1(X20,X23,X24)),X25)
        | X25 != X26
        | X25 != X27
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(k1_tsep_1(X20,X23,X24)))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X20)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( r1_tmap_1(X24,X21,k2_tmap_1(X20,X21,X22,X24),X27)
        | ~ r1_tmap_1(k1_tsep_1(X20,X23,X24),X21,k2_tmap_1(X20,X21,X22,k1_tsep_1(X20,X23,X24)),X25)
        | X25 != X26
        | X25 != X27
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(k1_tsep_1(X20,X23,X24)))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X20)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) )
      & ( ~ r1_tmap_1(X23,X21,k2_tmap_1(X20,X21,X22,X23),X26)
        | ~ r1_tmap_1(X24,X21,k2_tmap_1(X20,X21,X22,X24),X27)
        | r1_tmap_1(k1_tsep_1(X20,X23,X24),X21,k2_tmap_1(X20,X21,X22,k1_tsep_1(X20,X23,X24)),X25)
        | X25 != X26
        | X25 != X27
        | ~ m1_subset_1(X27,u1_struct_0(X24))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ m1_subset_1(X25,u1_struct_0(k1_tsep_1(X20,X23,X24)))
        | v2_struct_0(X24)
        | ~ m1_pre_topc(X24,X20)
        | v2_struct_0(X23)
        | ~ m1_pre_topc(X23,X20)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21))))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21)
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).

cnf(c_0_21,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_24,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_25,negated_conjecture,
    ( m1_connsp_2(esk1_2(esk2_0,esk7_0),esk2_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_26,plain,
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

cnf(c_0_27,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X6,X1,X4)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X6,u1_struct_0(X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_21,c_0_22])]),c_0_23])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk1_2(esk2_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_25]),c_0_17]),c_0_18]),c_0_16])]),c_0_19])).

cnf(c_0_30,plain,
    ( r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)
    | ~ r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))
    | ~ v1_funct_1(X5)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))
    | ~ m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))
    | ~ m1_subset_1(X6,u1_struct_0(X3))
    | ~ m1_subset_1(X6,u1_struct_0(X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( r1_tmap_1(esk2_0,X1,X2,esk7_0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,X1,k2_tmap_1(esk2_0,X1,X2,X3),esk7_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X3,esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(esk1_2(esk2_0,esk7_0),u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))
    | ~ m1_subset_1(esk7_0,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk1_2(esk2_0,esk7_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_39,plain,(
    ! [X29,X30,X31,X32,X33,X34] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,u1_struct_0(X30),u1_struct_0(X29))
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X32,X30)
      | ~ m1_subset_1(X33,u1_struct_0(X30))
      | ~ m1_subset_1(X34,u1_struct_0(X32))
      | X33 != X34
      | ~ r1_tmap_1(X30,X29,X31,X33)
      | r1_tmap_1(X32,X29,k2_tmap_1(X30,X29,X31,X32),X34) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_40,negated_conjecture,
    ( r1_tmap_1(k1_tsep_1(esk2_0,X1,X2),esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,k1_tsep_1(esk2_0,X1,X2)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X2,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X2),X3)
    | ~ r1_tmap_1(X1,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X1),X3)
    | ~ m1_pre_topc(X2,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(esk2_0,X1,X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_17]),c_0_33]),c_0_18]),c_0_34]),c_0_35])]),c_0_36]),c_0_19])).

cnf(c_0_41,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_44,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( r1_tmap_1(esk2_0,X1,X2,esk7_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk2_0,X1,k2_tmap_1(esk2_0,X1,X2,esk2_0),esk7_0)
    | ~ v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk2_0,esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_16])]),c_0_19])).

fof(c_0_46,plain,(
    ! [X28] :
      ( ~ l1_pre_topc(X28)
      | m1_pre_topc(X28,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r1_tmap_1(k1_tsep_1(esk2_0,X1,esk6_0),esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,k1_tsep_1(esk2_0,X1,esk6_0)),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),X2)
    | ~ r1_tmap_1(X1,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X1),X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk2_0,X1,esk6_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])).

cnf(c_0_49,negated_conjecture,
    ( esk2_0 = k1_tsep_1(esk2_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_43]),c_0_18])]),c_0_44]),c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0)
    | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( esk7_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_55,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_56,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)
    | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_57,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)
    | ~ r1_tmap_1(esk2_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk2_0),esk7_0)
    | ~ m1_pre_topc(esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35])]),c_0_36])).

cnf(c_0_58,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]),c_0_23])).

cnf(c_0_60,negated_conjecture,
    ( ~ r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)
    | ~ r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)
    | ~ r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk2_0),X1)
    | ~ r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),X1)
    | ~ r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_49]),c_0_49]),c_0_49]),c_0_44]),c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0)
    | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)
    | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_56,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)
    | ~ r1_tmap_1(esk2_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk2_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_18])])).

cnf(c_0_67,negated_conjecture,
    ( r1_tmap_1(X1,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk2_0,esk3_0,esk4_0,X2)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_31]),c_0_32]),c_0_17]),c_0_33]),c_0_18]),c_0_34]),c_0_35])]),c_0_36]),c_0_19])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0)
    | ~ r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_55]),c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_64])]),c_0_65]),c_0_66])).

cnf(c_0_70,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),X1)
    | ~ r1_tmap_1(esk2_0,esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_41]),c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),X1)
    | ~ r1_tmap_1(esk2_0,esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_43]),c_0_44])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)
    | ~ r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_69])])).

cnf(c_0_73,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_69]),c_0_63])])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_69]),c_0_64])])).

cnf(c_0_75,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_73])]),c_0_74])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:11:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.12/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.029 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t125_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_tmap_1)).
% 0.12/0.37  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.12/0.37  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.12/0.37  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.12/0.37  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.12/0.37  fof(t124_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>![X6]:(m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X4,X5)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(k1_tsep_1(X1,X4,X5),X2,k2_tmap_1(X1,X2,X3,k1_tsep_1(X1,X4,X5)),X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_tmap_1)).
% 0.12/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.37  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.12/0.37  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.12/0.37  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:((~(v2_struct_0(X5))&m1_pre_topc(X5,X1))=>(X1=k1_tsep_1(X1,X4,X5)=>![X6]:(m1_subset_1(X6,u1_struct_0(X1))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X5))=>((X6=X7&X6=X8)=>(r1_tmap_1(X1,X2,X3,X6)<=>(r1_tmap_1(X4,X2,k2_tmap_1(X1,X2,X3,X4),X7)&r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X8)))))))))))))), inference(assume_negation,[status(cth)],[t125_tmap_1])).
% 0.12/0.37  fof(c_0_10, plain, ![X17, X18]:(v2_struct_0(X17)|~v2_pre_topc(X17)|~l1_pre_topc(X17)|~m1_subset_1(X18,u1_struct_0(X17))|m1_connsp_2(esk1_2(X17,X18),X17,X18)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.12/0.37  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk2_0))&(esk2_0=k1_tsep_1(esk2_0,esk5_0,esk6_0)&(m1_subset_1(esk7_0,u1_struct_0(esk2_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk6_0))&((esk7_0=esk8_0&esk7_0=esk9_0)&((~r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)|(~r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)|~r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0)))&((r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)|r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0))&(r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0)|r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)))))))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])).
% 0.12/0.37  fof(c_0_12, plain, ![X35, X36, X37, X38, X39, X40, X41]:((~r1_tmap_1(X36,X35,X37,X40)|r1_tmap_1(X38,X35,k2_tmap_1(X36,X35,X37,X38),X41)|(~r1_tarski(X39,u1_struct_0(X38))|~m1_connsp_2(X39,X36,X40)|X40!=X41)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X38)|~m1_pre_topc(X38,X36))|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r1_tmap_1(X38,X35,k2_tmap_1(X36,X35,X37,X38),X41)|r1_tmap_1(X36,X35,X37,X40)|(~r1_tarski(X39,u1_struct_0(X38))|~m1_connsp_2(X39,X36,X40)|X40!=X41)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X36)))|(v2_struct_0(X38)|~m1_pre_topc(X38,X36))|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X36),u1_struct_0(X35))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X36),u1_struct_0(X35)))))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.12/0.37  fof(c_0_13, plain, ![X14, X15, X16]:(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|~m1_subset_1(X15,u1_struct_0(X14))|(~m1_connsp_2(X16,X14,X15)|m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.12/0.37  fof(c_0_14, plain, ![X11, X12, X13]:(v2_struct_0(X11)|~l1_pre_topc(X11)|(v2_struct_0(X12)|~m1_pre_topc(X12,X11)|(~m1_subset_1(X13,u1_struct_0(X12))|m1_subset_1(X13,u1_struct_0(X11))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.12/0.37  cnf(c_0_15, plain, (v2_struct_0(X1)|m1_connsp_2(esk1_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.12/0.37  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  fof(c_0_20, plain, ![X20, X21, X22, X23, X24, X25, X26, X27]:(((r1_tmap_1(X23,X21,k2_tmap_1(X20,X21,X22,X23),X26)|~r1_tmap_1(k1_tsep_1(X20,X23,X24),X21,k2_tmap_1(X20,X21,X22,k1_tsep_1(X20,X23,X24)),X25)|(X25!=X26|X25!=X27)|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(k1_tsep_1(X20,X23,X24)))|(v2_struct_0(X24)|~m1_pre_topc(X24,X20))|(v2_struct_0(X23)|~m1_pre_topc(X23,X20))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))&(r1_tmap_1(X24,X21,k2_tmap_1(X20,X21,X22,X24),X27)|~r1_tmap_1(k1_tsep_1(X20,X23,X24),X21,k2_tmap_1(X20,X21,X22,k1_tsep_1(X20,X23,X24)),X25)|(X25!=X26|X25!=X27)|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(k1_tsep_1(X20,X23,X24)))|(v2_struct_0(X24)|~m1_pre_topc(X24,X20))|(v2_struct_0(X23)|~m1_pre_topc(X23,X20))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20))))&(~r1_tmap_1(X23,X21,k2_tmap_1(X20,X21,X22,X23),X26)|~r1_tmap_1(X24,X21,k2_tmap_1(X20,X21,X22,X24),X27)|r1_tmap_1(k1_tsep_1(X20,X23,X24),X21,k2_tmap_1(X20,X21,X22,k1_tsep_1(X20,X23,X24)),X25)|(X25!=X26|X25!=X27)|~m1_subset_1(X27,u1_struct_0(X24))|~m1_subset_1(X26,u1_struct_0(X23))|~m1_subset_1(X25,u1_struct_0(k1_tsep_1(X20,X23,X24)))|(v2_struct_0(X24)|~m1_pre_topc(X24,X20))|(v2_struct_0(X23)|~m1_pre_topc(X23,X20))|(~v1_funct_1(X22)|~v1_funct_2(X22,u1_struct_0(X20),u1_struct_0(X21))|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X20),u1_struct_0(X21)))))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21))|(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t124_tmap_1])])])])])).
% 0.12/0.37  cnf(c_0_21, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.37  cnf(c_0_22, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.37  cnf(c_0_23, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.37  fof(c_0_24, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (m1_connsp_2(esk1_2(esk2_0,esk7_0),esk2_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_26, plain, (r1_tmap_1(k1_tsep_1(X3,X1,X6),X2,k2_tmap_1(X3,X2,X4,k1_tsep_1(X3,X1,X6)),X8)|v2_struct_0(X6)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tmap_1(X6,X2,k2_tmap_1(X3,X2,X4,X6),X7)|X8!=X5|X8!=X7|~m1_subset_1(X7,u1_struct_0(X6))|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X8,u1_struct_0(k1_tsep_1(X3,X1,X6)))|~m1_pre_topc(X6,X3)|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.37  cnf(c_0_27, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~r1_tarski(X6,u1_struct_0(X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_21, c_0_22])]), c_0_23])).
% 0.12/0.37  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk1_2(esk2_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_25]), c_0_17]), c_0_18]), c_0_16])]), c_0_19])).
% 0.12/0.37  cnf(c_0_30, plain, (r1_tmap_1(k1_tsep_1(X1,X2,X3),X4,k2_tmap_1(X1,X4,X5,k1_tsep_1(X1,X2,X3)),X6)|v2_struct_0(X3)|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X2)|~r1_tmap_1(X3,X4,k2_tmap_1(X1,X4,X5,X3),X6)|~r1_tmap_1(X2,X4,k2_tmap_1(X1,X4,X5,X2),X6)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X4))|~v1_funct_1(X5)|~v2_pre_topc(X1)|~v2_pre_topc(X4)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X4)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X4))))|~m1_subset_1(X6,u1_struct_0(k1_tsep_1(X1,X2,X3)))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X6,u1_struct_0(X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_26])])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_36, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (r1_tmap_1(esk2_0,X1,X2,esk7_0)|v2_struct_0(X1)|v2_struct_0(X3)|~r1_tmap_1(X3,X1,k2_tmap_1(esk2_0,X1,X2,X3),esk7_0)|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))|~v1_funct_1(X2)|~v2_pre_topc(X1)|~m1_pre_topc(X3,esk2_0)|~l1_pre_topc(X1)|~r1_tarski(esk1_2(esk2_0,esk7_0),u1_struct_0(X3))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))|~m1_subset_1(esk7_0,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_17]), c_0_18])]), c_0_19])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(esk1_2(esk2_0,esk7_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.12/0.37  fof(c_0_39, plain, ![X29, X30, X31, X32, X33, X34]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))|(v2_struct_0(X32)|~m1_pre_topc(X32,X30)|(~m1_subset_1(X33,u1_struct_0(X30))|(~m1_subset_1(X34,u1_struct_0(X32))|(X33!=X34|~r1_tmap_1(X30,X29,X31,X33)|r1_tmap_1(X32,X29,k2_tmap_1(X30,X29,X31,X32),X34)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk2_0,X1,X2),esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,k1_tsep_1(esk2_0,X1,X2)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~r1_tmap_1(X2,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X2),X3)|~r1_tmap_1(X1,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X1),X3)|~m1_pre_topc(X2,esk2_0)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(X3,u1_struct_0(k1_tsep_1(esk2_0,X1,X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_17]), c_0_33]), c_0_18]), c_0_34]), c_0_35])]), c_0_36]), c_0_19])).
% 0.12/0.37  cnf(c_0_41, negated_conjecture, (m1_pre_topc(esk6_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_44, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (r1_tmap_1(esk2_0,X1,X2,esk7_0)|v2_struct_0(X1)|~r1_tmap_1(esk2_0,X1,k2_tmap_1(esk2_0,X1,X2,esk2_0),esk7_0)|~v1_funct_2(X2,u1_struct_0(esk2_0),u1_struct_0(X1))|~v1_funct_1(X2)|~v2_pre_topc(X1)|~m1_pre_topc(esk2_0,esk2_0)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(X1))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_16])]), c_0_19])).
% 0.12/0.37  fof(c_0_46, plain, ![X28]:(~l1_pre_topc(X28)|m1_pre_topc(X28,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.12/0.37  cnf(c_0_47, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (r1_tmap_1(k1_tsep_1(esk2_0,X1,esk6_0),esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,k1_tsep_1(esk2_0,X1,esk6_0)),X2)|v2_struct_0(X1)|~r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),X2)|~r1_tmap_1(X1,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X1),X2)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(X2,u1_struct_0(k1_tsep_1(esk2_0,X1,esk6_0)))|~m1_subset_1(X2,u1_struct_0(esk6_0))|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])).
% 0.12/0.37  cnf(c_0_49, negated_conjecture, (esk2_0=k1_tsep_1(esk2_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_43]), c_0_18])]), c_0_44]), c_0_19])).
% 0.12/0.37  cnf(c_0_51, negated_conjecture, (r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0)|r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_52, negated_conjecture, (esk7_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_54, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_56, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)|r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)|~r1_tmap_1(esk2_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk2_0),esk7_0)|~m1_pre_topc(esk2_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35])]), c_0_36])).
% 0.12/0.37  cnf(c_0_58, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.37  cnf(c_0_59, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_47]), c_0_23])).
% 0.12/0.37  cnf(c_0_60, negated_conjecture, (~r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)|~r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk8_0)|~r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (r1_tmap_1(esk2_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk2_0),X1)|~r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),X1)|~r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_43]), c_0_49]), c_0_49]), c_0_49]), c_0_44]), c_0_50])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0)|r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.12/0.37  cnf(c_0_63, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk6_0))), inference(rw,[status(thm)],[c_0_53, c_0_52])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_54, c_0_55])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)|r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[c_0_56, c_0_55])).
% 0.12/0.37  cnf(c_0_66, negated_conjecture, (r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)|~r1_tmap_1(esk2_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk2_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_18])])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (r1_tmap_1(X1,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk2_0,esk3_0,esk4_0,X2)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_31]), c_0_32]), c_0_17]), c_0_33]), c_0_18]), c_0_34]), c_0_35])]), c_0_36]), c_0_19])).
% 0.12/0.37  cnf(c_0_68, negated_conjecture, (~r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)|~r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0)|~r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_55]), c_0_52])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (r1_tmap_1(esk2_0,esk3_0,esk4_0,esk7_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_64])]), c_0_65]), c_0_66])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, (r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),X1)|~r1_tmap_1(esk2_0,esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_41]), c_0_42])).
% 0.12/0.37  cnf(c_0_71, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),X1)|~r1_tmap_1(esk2_0,esk3_0,esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_43]), c_0_44])).
% 0.12/0.37  cnf(c_0_72, negated_conjecture, (~r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)|~r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_69])])).
% 0.12/0.37  cnf(c_0_73, negated_conjecture, (r1_tmap_1(esk6_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_69]), c_0_63])])).
% 0.12/0.37  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,k2_tmap_1(esk2_0,esk3_0,esk4_0,esk5_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_69]), c_0_64])])).
% 0.12/0.37  cnf(c_0_75, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_73])]), c_0_74])]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 76
% 0.12/0.37  # Proof object clause steps            : 57
% 0.12/0.37  # Proof object formula steps           : 19
% 0.12/0.37  # Proof object conjectures             : 49
% 0.12/0.37  # Proof object clause conjectures      : 46
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 30
% 0.12/0.37  # Proof object initial formulas used   : 9
% 0.12/0.37  # Proof object generating inferences   : 17
% 0.12/0.37  # Proof object simplifying inferences  : 82
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 9
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 34
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 34
% 0.12/0.37  # Processed clauses                    : 123
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 4
% 0.12/0.37  # ...remaining for further processing  : 118
% 0.12/0.37  # Other redundant clauses eliminated   : 9
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 1
% 0.12/0.37  # Backward-rewritten                   : 5
% 0.12/0.37  # Generated clauses                    : 65
% 0.12/0.37  # ...of the previous two non-trivial   : 62
% 0.12/0.37  # Contextual simplify-reflections      : 17
% 0.12/0.37  # Paramodulations                      : 59
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 9
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 73
% 0.12/0.37  #    Positive orientable unit clauses  : 22
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 4
% 0.12/0.37  #    Non-unit-clauses                  : 47
% 0.12/0.37  # Current number of unprocessed clauses: 6
% 0.12/0.37  # ...number of literals in the above   : 29
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 39
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 2703
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 409
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 22
% 0.12/0.37  # Unit Clause-clause subsumption calls : 80
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 9
% 0.12/0.37  # BW rewrite match successes           : 2
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 8712
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.044 s
% 0.12/0.37  # System time              : 0.004 s
% 0.12/0.37  # Total time               : 0.048 s
% 0.12/0.37  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
