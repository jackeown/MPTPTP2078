%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:03 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 459 expanded)
%              Number of clauses        :   55 ( 158 expanded)
%              Number of leaves         :   13 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  389 (4985 expanded)
%              Number of equality atoms :   27 ( 481 expanded)
%              Maximal formula depth    :   32 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t88_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X3))
                               => ( ( X6 = X7
                                    & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                 => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t83_tmap_1,axiom,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
                           => ! [X7] :
                                ( m1_subset_1(X7,u1_struct_0(X4))
                               => ! [X8] :
                                    ( m1_subset_1(X8,u1_struct_0(X3))
                                   => ( ( r1_tarski(X6,u1_struct_0(X3))
                                        & m1_connsp_2(X6,X4,X7)
                                        & X7 = X8 )
                                     => ( r1_tmap_1(X4,X2,X5,X7)
                                      <=> r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

fof(t7_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X2)
             => m1_pre_topc(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_13,negated_conjecture,(
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
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = X4
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X4))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X3))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7) )
                                   => r1_tmap_1(X4,X2,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t88_tmap_1])).

fof(c_0_14,plain,(
    ! [X26,X27,X28] :
      ( ( ~ m1_pre_topc(X27,X26)
        | m1_pre_topc(X28,X26)
        | X27 != g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) )
      & ( ~ m1_pre_topc(X28,X26)
        | m1_pre_topc(X27,X26)
        | X27 != g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

fof(c_0_15,plain,(
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk2_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk2_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))
    & g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = esk5_0
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk8_0,u1_struct_0(esk4_0))
    & esk7_0 = esk8_0
    & r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)
    & ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

cnf(c_0_18,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_24,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41,X42] :
      ( ( ~ r1_tmap_1(X38,X36,X39,X41)
        | r1_tmap_1(X37,X36,k3_tmap_1(X35,X36,X38,X37,X39),X42)
        | ~ r1_tarski(X40,u1_struct_0(X37))
        | ~ m1_connsp_2(X40,X38,X41)
        | X41 != X42
        | ~ m1_subset_1(X42,u1_struct_0(X37))
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ m1_pre_topc(X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X38),u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36))))
        | v2_struct_0(X38)
        | ~ m1_pre_topc(X38,X35)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ r1_tmap_1(X37,X36,k3_tmap_1(X35,X36,X38,X37,X39),X42)
        | r1_tmap_1(X38,X36,X39,X41)
        | ~ r1_tarski(X40,u1_struct_0(X37))
        | ~ m1_connsp_2(X40,X38,X41)
        | X41 != X42
        | ~ m1_subset_1(X42,u1_struct_0(X37))
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ m1_pre_topc(X37,X38)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X38),u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36))))
        | v2_struct_0(X38)
        | ~ m1_pre_topc(X38,X35)
        | v2_struct_0(X37)
        | ~ m1_pre_topc(X37,X35)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_tmap_1])])])])])).

fof(c_0_25,plain,(
    ! [X32,X33,X34] :
      ( ~ v2_pre_topc(X32)
      | ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | ~ m1_pre_topc(X34,X33)
      | m1_pre_topc(X34,X32) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X3) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_20]),c_0_21]),c_0_23])])).

fof(c_0_30,plain,(
    ! [X29] :
      ( ~ l1_pre_topc(X29)
      | m1_pre_topc(X29,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_31,plain,
    ( r1_tmap_1(X4,X2,X5,X7)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)
    | ~ r1_tarski(X8,u1_struct_0(X1))
    | ~ m1_connsp_2(X8,X4,X7)
    | X7 != X6
    | ~ m1_subset_1(X6,u1_struct_0(X1))
    | ~ m1_subset_1(X7,u1_struct_0(X4))
    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X1,X4)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | X2 != esk5_0
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_34,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_36,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_connsp_2(X22,X20,X21)
      | m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_37,plain,(
    ! [X9,X10] :
      ( ( r1_tarski(X9,X10)
        | X9 != X10 )
      & ( r1_tarski(X10,X9)
        | X9 != X10 )
      & ( ~ r1_tarski(X9,X10)
        | ~ r1_tarski(X10,X9)
        | X9 = X10 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X30,X31] :
      ( ~ l1_pre_topc(X30)
      | ~ m1_pre_topc(X31,X30)
      | r1_tarski(u1_struct_0(X31),u1_struct_0(X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

fof(c_0_39,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
      | m1_pre_topc(X19,X18) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_40,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X6)
    | ~ r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X7,X1,X4)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_pre_topc(X6,X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X6))
    | ~ r1_tarski(X7,u1_struct_0(X6)) ),
    inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31,c_0_32])])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( esk7_0 = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk4_0,X1)
    | X1 != esk5_0
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_35]),c_0_21]),c_0_23])])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_35]),c_0_21])])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_56,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | m1_connsp_2(esk1_2(X23,X24),X23,X24) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_58,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_59,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_60,plain,(
    ! [X11,X12] :
      ( ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
        | r1_tarski(X11,X12) )
      & ( ~ r1_tarski(X11,X12)
        | m1_subset_1(X11,k1_zfmisc_1(X12)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ r1_tmap_1(X3,esk3_0,k3_tmap_1(X2,esk3_0,esk5_0,X3,esk6_0),X1)
    | ~ m1_connsp_2(X4,esk5_0,X1)
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(X3,esk5_0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r1_tarski(X4,u1_struct_0(X3)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45])]),c_0_46]),c_0_47])).

cnf(c_0_62,negated_conjecture,
    ( r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_63,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_53,c_0_49])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_52]),c_0_51])]),c_0_47])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk1_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_70,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_71,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_59,c_0_34])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( ~ m1_connsp_2(X1,esk5_0,esk7_0)
    | ~ r1_tarski(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_35]),c_0_63]),c_0_21]),c_0_23]),c_0_55]),c_0_64])]),c_0_65]),c_0_66]),c_0_67]),c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( m1_connsp_2(esk1_2(esk5_0,esk7_0),esk5_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_55]),c_0_52]),c_0_51])]),c_0_47])).

cnf(c_0_75,plain,
    ( u1_struct_0(X1) = u1_struct_0(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_58]),c_0_19])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_27]),c_0_52]),c_0_28])])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk5_0))
    | ~ m1_connsp_2(X1,esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( ~ r1_tarski(esk1_2(esk5_0,esk7_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_63]),c_0_76]),c_0_28])])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk1_2(esk5_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:45:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.12/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.029 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t88_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 0.12/0.39  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.12/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.12/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.12/0.39  fof(t83_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>![X6]:(m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>![X8]:(m1_subset_1(X8,u1_struct_0(X3))=>(((r1_tarski(X6,u1_struct_0(X3))&m1_connsp_2(X6,X4,X7))&X7=X8)=>(r1_tmap_1(X4,X2,X5,X7)<=>r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X8)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 0.12/0.39  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.12/0.39  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.12/0.39  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.12/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.39  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.12/0.39  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.12/0.39  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.12/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.12/0.39  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))=>(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=X4=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>![X7]:(m1_subset_1(X7,u1_struct_0(X3))=>((X6=X7&r1_tmap_1(X3,X2,k3_tmap_1(X1,X2,X4,X3,X5),X7))=>r1_tmap_1(X4,X2,X5,X6))))))))))), inference(assume_negation,[status(cth)],[t88_tmap_1])).
% 0.12/0.39  fof(c_0_14, plain, ![X26, X27, X28]:((~m1_pre_topc(X27,X26)|m1_pre_topc(X28,X26)|X27!=g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))|(~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27))|~l1_pre_topc(X26))&(~m1_pre_topc(X28,X26)|m1_pre_topc(X27,X26)|X27!=g1_pre_topc(u1_struct_0(X28),u1_pre_topc(X28))|(~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27))|~l1_pre_topc(X26))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.12/0.39  fof(c_0_15, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.12/0.39  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk2_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk2_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0)))))&(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=esk5_0&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk4_0))&((esk7_0=esk8_0&r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0))&~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.12/0.39  fof(c_0_17, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.12/0.39  cnf(c_0_18, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_19, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_22, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  fof(c_0_24, plain, ![X35, X36, X37, X38, X39, X40, X41, X42]:((~r1_tmap_1(X38,X36,X39,X41)|r1_tmap_1(X37,X36,k3_tmap_1(X35,X36,X38,X37,X39),X42)|(~r1_tarski(X40,u1_struct_0(X37))|~m1_connsp_2(X40,X38,X41)|X41!=X42)|~m1_subset_1(X42,u1_struct_0(X37))|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~m1_pre_topc(X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X38),u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36)))))|(v2_struct_0(X38)|~m1_pre_topc(X38,X35))|(v2_struct_0(X37)|~m1_pre_topc(X37,X35))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~r1_tmap_1(X37,X36,k3_tmap_1(X35,X36,X38,X37,X39),X42)|r1_tmap_1(X38,X36,X39,X41)|(~r1_tarski(X40,u1_struct_0(X37))|~m1_connsp_2(X40,X38,X41)|X41!=X42)|~m1_subset_1(X42,u1_struct_0(X37))|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~m1_pre_topc(X37,X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X38),u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36)))))|(v2_struct_0(X38)|~m1_pre_topc(X38,X35))|(v2_struct_0(X37)|~m1_pre_topc(X37,X35))|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t83_tmap_1])])])])])).
% 0.12/0.39  fof(c_0_25, plain, ![X32, X33, X34]:(~v2_pre_topc(X32)|~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|(~m1_pre_topc(X34,X33)|m1_pre_topc(X34,X32)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.12/0.39  cnf(c_0_26, plain, (m1_pre_topc(X1,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X3)), inference(csr,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=esk5_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_20]), c_0_21]), c_0_23])])).
% 0.12/0.39  fof(c_0_30, plain, ![X29]:(~l1_pre_topc(X29)|m1_pre_topc(X29,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.12/0.39  cnf(c_0_31, plain, (r1_tmap_1(X4,X2,X5,X7)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X1,X2,k3_tmap_1(X3,X2,X4,X1,X5),X6)|~r1_tarski(X8,u1_struct_0(X1))|~m1_connsp_2(X8,X4,X7)|X7!=X6|~m1_subset_1(X6,u1_struct_0(X1))|~m1_subset_1(X7,u1_struct_0(X4))|~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X4)))|~m1_pre_topc(X1,X4)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.39  cnf(c_0_32, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (m1_pre_topc(esk4_0,X1)|X2!=esk5_0|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])])).
% 0.12/0.39  cnf(c_0_34, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk5_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  fof(c_0_36, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))|(~m1_connsp_2(X22,X20,X21)|m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.12/0.39  fof(c_0_37, plain, ![X9, X10]:(((r1_tarski(X9,X10)|X9!=X10)&(r1_tarski(X10,X9)|X9!=X10))&(~r1_tarski(X9,X10)|~r1_tarski(X10,X9)|X9=X10)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.39  fof(c_0_38, plain, ![X30, X31]:(~l1_pre_topc(X30)|(~m1_pre_topc(X31,X30)|r1_tarski(u1_struct_0(X31),u1_struct_0(X30)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.12/0.39  fof(c_0_39, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|m1_pre_topc(X19,X18))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.12/0.39  cnf(c_0_40, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X5)|v2_struct_0(X2)|v2_struct_0(X6)|~r1_tmap_1(X6,X2,k3_tmap_1(X5,X2,X1,X6,X3),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X7,X1,X4)|~m1_pre_topc(X1,X5)|~m1_pre_topc(X6,X1)|~l1_pre_topc(X5)|~l1_pre_topc(X2)|~v2_pre_topc(X5)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X6))|~r1_tarski(X7,u1_struct_0(X6))), inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_31, c_0_32])])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_43, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_44, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_45, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_48, negated_conjecture, (r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (esk7_0=esk8_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk4_0,X1)|X1!=esk5_0|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.39  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_35]), c_0_21]), c_0_23])])).
% 0.12/0.39  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_35]), c_0_21])])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_54, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  fof(c_0_56, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))|m1_connsp_2(esk1_2(X23,X24),X23,X24)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.12/0.39  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.12/0.39  cnf(c_0_58, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.12/0.39  cnf(c_0_59, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.39  fof(c_0_60, plain, ![X11, X12]:((~m1_subset_1(X11,k1_zfmisc_1(X12))|r1_tarski(X11,X12))&(~r1_tarski(X11,X12)|m1_subset_1(X11,k1_zfmisc_1(X12)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.12/0.39  cnf(c_0_61, negated_conjecture, (r1_tmap_1(esk5_0,esk3_0,esk6_0,X1)|v2_struct_0(X2)|v2_struct_0(X3)|~r1_tmap_1(X3,esk3_0,k3_tmap_1(X2,esk3_0,esk5_0,X3,esk6_0),X1)|~m1_connsp_2(X4,esk5_0,X1)|~m1_pre_topc(esk5_0,X2)|~m1_pre_topc(X3,esk5_0)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_subset_1(X1,u1_struct_0(esk5_0))|~m1_subset_1(X1,u1_struct_0(X3))|~r1_tarski(X4,u1_struct_0(X3))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45])]), c_0_46]), c_0_47])).
% 0.12/0.39  cnf(c_0_62, negated_conjecture, (r1_tmap_1(esk4_0,esk3_0,k3_tmap_1(esk2_0,esk3_0,esk5_0,esk4_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, (m1_pre_topc(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.12/0.39  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk4_0))), inference(rw,[status(thm)],[c_0_53, c_0_49])).
% 0.12/0.39  cnf(c_0_65, negated_conjecture, (~r1_tmap_1(esk5_0,esk3_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_66, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_67, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~m1_connsp_2(X1,esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_52]), c_0_51])]), c_0_47])).
% 0.12/0.39  cnf(c_0_69, plain, (v2_struct_0(X1)|m1_connsp_2(esk1_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.12/0.39  cnf(c_0_70, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(u1_struct_0(X2),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.39  cnf(c_0_71, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_59, c_0_34])).
% 0.12/0.39  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.12/0.39  cnf(c_0_73, negated_conjecture, (~m1_connsp_2(X1,esk5_0,esk7_0)|~r1_tarski(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_35]), c_0_63]), c_0_21]), c_0_23]), c_0_55]), c_0_64])]), c_0_65]), c_0_66]), c_0_67]), c_0_68])).
% 0.12/0.39  cnf(c_0_74, negated_conjecture, (m1_connsp_2(esk1_2(esk5_0,esk7_0),esk5_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_55]), c_0_52]), c_0_51])]), c_0_47])).
% 0.12/0.39  cnf(c_0_75, plain, (u1_struct_0(X1)=u1_struct_0(X2)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_58]), c_0_19])).
% 0.12/0.39  cnf(c_0_76, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_27]), c_0_52]), c_0_28])])).
% 0.12/0.39  cnf(c_0_77, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk5_0))|~m1_connsp_2(X1,esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_72, c_0_68])).
% 0.12/0.39  cnf(c_0_78, negated_conjecture, (~r1_tarski(esk1_2(esk5_0,esk7_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.12/0.39  cnf(c_0_79, negated_conjecture, (u1_struct_0(esk4_0)=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_63]), c_0_76]), c_0_28])])).
% 0.12/0.39  cnf(c_0_80, negated_conjecture, (r1_tarski(esk1_2(esk5_0,esk7_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_77, c_0_74])).
% 0.12/0.39  cnf(c_0_81, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_79]), c_0_80])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 82
% 0.12/0.39  # Proof object clause steps            : 55
% 0.12/0.39  # Proof object formula steps           : 27
% 0.12/0.39  # Proof object conjectures             : 41
% 0.12/0.39  # Proof object clause conjectures      : 38
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 31
% 0.12/0.39  # Proof object initial formulas used   : 13
% 0.12/0.39  # Proof object generating inferences   : 19
% 0.12/0.39  # Proof object simplifying inferences  : 56
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 14
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 38
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 38
% 0.12/0.39  # Processed clauses                    : 284
% 0.12/0.39  # ...of these trivial                  : 28
% 0.12/0.39  # ...subsumed                          : 73
% 0.12/0.39  # ...remaining for further processing  : 183
% 0.12/0.39  # Other redundant clauses eliminated   : 4
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 5
% 0.12/0.39  # Backward-rewritten                   : 14
% 0.12/0.39  # Generated clauses                    : 582
% 0.12/0.39  # ...of the previous two non-trivial   : 365
% 0.12/0.39  # Contextual simplify-reflections      : 17
% 0.12/0.39  # Paramodulations                      : 570
% 0.12/0.39  # Factorizations                       : 6
% 0.12/0.39  # Equation resolutions                 : 6
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 123
% 0.12/0.39  #    Positive orientable unit clauses  : 27
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 5
% 0.12/0.39  #    Non-unit-clauses                  : 91
% 0.12/0.39  # Current number of unprocessed clauses: 153
% 0.12/0.39  # ...number of literals in the above   : 887
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 56
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 3132
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 919
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 94
% 0.12/0.39  # Unit Clause-clause subsumption calls : 4
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 5
% 0.12/0.39  # BW rewrite match successes           : 5
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 14628
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.048 s
% 0.12/0.39  # System time              : 0.007 s
% 0.12/0.39  # Total time               : 0.055 s
% 0.12/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
