%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:29 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 (1227 expanded)
%              Number of clauses        :   60 ( 420 expanded)
%              Number of leaves         :   14 ( 297 expanded)
%              Depth                    :   13
%              Number of atoms          :  524 (13305 expanded)
%              Number of equality atoms :   17 ( 696 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   44 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_tmap_1,conjecture,(
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
                    & v1_tsep_1(X4,X2)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( X5 = X6
                           => ( r1_tmap_1(X2,X1,X3,X5)
                            <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(t16_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_tsep_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v3_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t6_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( m1_connsp_2(X2,X1,X3)
               => r2_hidden(X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tmap_1)).

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

fof(t9_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( m1_connsp_2(X4,X1,X3)
                            & r1_tarski(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(c_0_14,negated_conjecture,(
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
                      & v1_tsep_1(X4,X2)
                      & m1_pre_topc(X4,X2) )
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X2))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X4))
                           => ( X5 = X6
                             => ( r1_tmap_1(X2,X1,X3,X5)
                              <=> r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_tmap_1])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))
    & ~ v2_struct_0(esk8_0)
    & v1_tsep_1(esk8_0,esk6_0)
    & m1_pre_topc(esk8_0,esk6_0)
    & m1_subset_1(esk9_0,u1_struct_0(esk6_0))
    & m1_subset_1(esk10_0,u1_struct_0(esk8_0))
    & esk9_0 = esk10_0
    & ( ~ r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)
      | ~ r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0) )
    & ( r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)
      | r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_16,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,plain,(
    ! [X16,X17] :
      ( ~ v2_pre_topc(X16)
      | ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | v2_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_tsep_1(X39,X38)
        | ~ m1_pre_topc(X39,X38)
        | v3_pre_topc(X40,X38)
        | X40 != u1_struct_0(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ m1_pre_topc(X39,X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( v1_tsep_1(X39,X38)
        | ~ v3_pre_topc(X40,X38)
        | X40 != u1_struct_0(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ m1_pre_topc(X39,X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_pre_topc(X39,X38)
        | ~ v3_pre_topc(X40,X38)
        | X40 != u1_struct_0(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ m1_pre_topc(X39,X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_19,plain,(
    ! [X29,X30,X31] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | ~ m1_connsp_2(X30,X29,X31)
      | r2_hidden(X31,X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_20,plain,(
    ! [X23,X24,X25] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | ~ m1_connsp_2(X25,X23,X24)
      | m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_21,plain,(
    ! [X26,X27] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | m1_connsp_2(esk2_2(X26,X27),X26,X27) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk10_0,u1_struct_0(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( esk9_0 = esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_30,plain,(
    ! [X41,X42] :
      ( ~ l1_pre_topc(X41)
      | ~ m1_pre_topc(X42,X41)
      | m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk2_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_26]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_38,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( m1_connsp_2(esk2_2(esk8_0,esk9_0),esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

fof(c_0_43,plain,(
    ! [X14,X15] :
      ( ( ~ m1_subset_1(X14,k1_zfmisc_1(X15))
        | r1_tarski(X14,X15) )
      & ( ~ r1_tarski(X14,X15)
        | m1_subset_1(X14,k1_zfmisc_1(X15)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_44,plain,(
    ! [X49,X50,X51,X52,X53,X54,X55] :
      ( ( ~ r1_tmap_1(X50,X49,X51,X54)
        | r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X55)
        | ~ r1_tarski(X53,u1_struct_0(X52))
        | ~ m1_connsp_2(X53,X50,X54)
        | X54 != X55
        | ~ m1_subset_1(X55,u1_struct_0(X52))
        | ~ m1_subset_1(X54,u1_struct_0(X50))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X50)))
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) )
      & ( ~ r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X55)
        | r1_tmap_1(X50,X49,X51,X54)
        | ~ r1_tarski(X53,u1_struct_0(X52))
        | ~ m1_connsp_2(X53,X50,X54)
        | X54 != X55
        | ~ m1_subset_1(X55,u1_struct_0(X52))
        | ~ m1_subset_1(X54,u1_struct_0(X50))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X50)))
        | v2_struct_0(X52)
        | ~ m1_pre_topc(X52,X50)
        | ~ v1_funct_1(X51)
        | ~ v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49))))
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50)
        | v2_struct_0(X49)
        | ~ v2_pre_topc(X49)
        | ~ l1_pre_topc(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

fof(c_0_45,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ l1_pre_topc(X20)
      | v2_struct_0(X21)
      | ~ m1_pre_topc(X21,X20)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | m1_subset_1(X22,u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_46,plain,(
    ! [X32,X33,X34,X37] :
      ( ( m1_subset_1(esk3_3(X32,X33,X34),k1_zfmisc_1(u1_struct_0(X32)))
        | ~ r2_hidden(X34,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_connsp_2(esk3_3(X32,X33,X34),X32,X34)
        | ~ r2_hidden(X34,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r1_tarski(esk3_3(X32,X33,X34),X33)
        | ~ r2_hidden(X34,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( m1_subset_1(esk4_2(X32,X33),u1_struct_0(X32))
        | v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( r2_hidden(esk4_2(X32,X33),X33)
        | v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) )
      & ( ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X32)))
        | ~ m1_connsp_2(X37,X32,esk4_2(X32,X33))
        | ~ r1_tarski(X37,X33)
        | v3_pre_topc(X33,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))
        | v2_struct_0(X32)
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_connsp_2])])])])])])).

cnf(c_0_47,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]),c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( v1_tsep_1(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk9_0,esk2_2(esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_35]),c_0_36]),c_0_34])]),c_0_37])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk2_2(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_42]),c_0_35]),c_0_36]),c_0_34])]),c_0_37])).

cnf(c_0_53,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_55,plain,
    ( m1_connsp_2(esk3_3(X1,X2,X3),X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk8_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_25]),c_0_26]),c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_25]),c_0_26])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk9_0,X1)
    | ~ r1_tarski(esk2_2(esk8_0,esk9_0),X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk2_2(esk8_0,esk9_0),u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_61,plain,(
    ! [X43,X44,X45,X46,X47,X48] :
      ( v2_struct_0(X43)
      | ~ v2_pre_topc(X43)
      | ~ l1_pre_topc(X43)
      | v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | ~ v1_funct_1(X45)
      | ~ v1_funct_2(X45,u1_struct_0(X44),u1_struct_0(X43))
      | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))
      | v2_struct_0(X46)
      | ~ m1_pre_topc(X46,X44)
      | ~ m1_subset_1(X47,u1_struct_0(X44))
      | ~ m1_subset_1(X48,u1_struct_0(X46))
      | X47 != X48
      | ~ r1_tmap_1(X44,X43,X45,X47)
      | r1_tmap_1(X46,X43,k2_tmap_1(X44,X43,X45,X46),X48) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_62,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_connsp_2(X6,X1,X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ r1_tarski(X6,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_53,c_0_32])]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(esk3_3(esk6_0,u1_struct_0(esk8_0),X1),esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_26]),c_0_28]),c_0_57])]),c_0_58])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk9_0,u1_struct_0(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_72,plain,
    ( r1_tarski(esk3_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_73,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk7_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X2),X1)
    | ~ m1_connsp_2(X3,esk6_0,X1)
    | ~ m1_pre_topc(X2,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64]),c_0_26]),c_0_65]),c_0_28]),c_0_66]),c_0_67])]),c_0_68]),c_0_58])).

cnf(c_0_75,negated_conjecture,
    ( m1_connsp_2(esk3_3(esk6_0,u1_struct_0(esk8_0),esk9_0),esk6_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk3_3(esk6_0,u1_struct_0(esk8_0),X1),u1_struct_0(esk8_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,u1_struct_0(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_56]),c_0_26]),c_0_28]),c_0_57])]),c_0_58])).

cnf(c_0_77,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)
    | r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_78,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_54])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(X1,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X1),esk9_0)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(esk9_0,u1_struct_0(X1))
    | ~ r1_tarski(esk3_3(esk6_0,u1_struct_0(esk8_0),esk9_0),u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk3_3(esk6_0,u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_70]),c_0_71])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk9_0)
    | r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)
    | ~ r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk6_0,esk5_0,esk7_0,X2)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_63]),c_0_64]),c_0_26]),c_0_65]),c_0_28]),c_0_66]),c_0_67])]),c_0_68]),c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_25]),c_0_34])]),c_0_37]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk9_0)
    | ~ r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_23])).

cnf(c_0_86,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X1),esk9_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(esk9_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_25]),c_0_34])]),c_0_87]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:56:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.21/0.40  # and selection function SelectCQIPrecWNTNp.
% 0.21/0.40  #
% 0.21/0.40  # Preprocessing time       : 0.030 s
% 0.21/0.40  # Presaturation interreduction done
% 0.21/0.40  
% 0.21/0.40  # Proof found!
% 0.21/0.40  # SZS status Theorem
% 0.21/0.40  # SZS output start CNFRefutation
% 0.21/0.40  fof(t67_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.21/0.40  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.40  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.21/0.40  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.21/0.40  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.21/0.40  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.21/0.40  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.21/0.40  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.21/0.40  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.21/0.40  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.21/0.40  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.21/0.40  fof(t9_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.21/0.40  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.21/0.40  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))))), inference(assume_negation,[status(cth)],[t67_tmap_1])).
% 0.21/0.40  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)))))&(((~v2_struct_0(esk8_0)&v1_tsep_1(esk8_0,esk6_0))&m1_pre_topc(esk8_0,esk6_0))&(m1_subset_1(esk9_0,u1_struct_0(esk6_0))&(m1_subset_1(esk10_0,u1_struct_0(esk8_0))&(esk9_0=esk10_0&((~r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)|~r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0))&(r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)|r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.21/0.40  fof(c_0_16, plain, ![X18, X19]:(~l1_pre_topc(X18)|(~m1_pre_topc(X19,X18)|l1_pre_topc(X19))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.40  fof(c_0_17, plain, ![X16, X17]:(~v2_pre_topc(X16)|~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|v2_pre_topc(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.21/0.40  fof(c_0_18, plain, ![X38, X39, X40]:((~v1_tsep_1(X39,X38)|~m1_pre_topc(X39,X38)|v3_pre_topc(X40,X38)|X40!=u1_struct_0(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~m1_pre_topc(X39,X38)|(~v2_pre_topc(X38)|~l1_pre_topc(X38)))&((v1_tsep_1(X39,X38)|~v3_pre_topc(X40,X38)|X40!=u1_struct_0(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~m1_pre_topc(X39,X38)|(~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(m1_pre_topc(X39,X38)|~v3_pre_topc(X40,X38)|X40!=u1_struct_0(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|~m1_pre_topc(X39,X38)|(~v2_pre_topc(X38)|~l1_pre_topc(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.21/0.40  fof(c_0_19, plain, ![X29, X30, X31]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_subset_1(X31,u1_struct_0(X29))|(~m1_connsp_2(X30,X29,X31)|r2_hidden(X31,X30))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.21/0.40  fof(c_0_20, plain, ![X23, X24, X25]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))|(~m1_connsp_2(X25,X23,X24)|m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.21/0.40  fof(c_0_21, plain, ![X26, X27]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,u1_struct_0(X26))|m1_connsp_2(esk2_2(X26,X27),X26,X27)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.21/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk10_0,u1_struct_0(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_23, negated_conjecture, (esk9_0=esk10_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.40  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_27, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.40  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_29, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.40  fof(c_0_30, plain, ![X41, X42]:(~l1_pre_topc(X41)|(~m1_pre_topc(X42,X41)|m1_subset_1(u1_struct_0(X42),k1_zfmisc_1(u1_struct_0(X41))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.40  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.40  cnf(c_0_32, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.40  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_connsp_2(esk2_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.40  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk8_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.21/0.40  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.21/0.40  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_26]), c_0_28])])).
% 0.21/0.40  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_38, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_29])).
% 0.21/0.40  cnf(c_0_39, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.40  fof(c_0_40, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.21/0.40  cnf(c_0_41, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.40  cnf(c_0_42, negated_conjecture, (m1_connsp_2(esk2_2(esk8_0,esk9_0),esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.21/0.40  fof(c_0_43, plain, ![X14, X15]:((~m1_subset_1(X14,k1_zfmisc_1(X15))|r1_tarski(X14,X15))&(~r1_tarski(X14,X15)|m1_subset_1(X14,k1_zfmisc_1(X15)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.21/0.40  fof(c_0_44, plain, ![X49, X50, X51, X52, X53, X54, X55]:((~r1_tmap_1(X50,X49,X51,X54)|r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X55)|(~r1_tarski(X53,u1_struct_0(X52))|~m1_connsp_2(X53,X50,X54)|X54!=X55)|~m1_subset_1(X55,u1_struct_0(X52))|~m1_subset_1(X54,u1_struct_0(X50))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X50)))|(v2_struct_0(X52)|~m1_pre_topc(X52,X50))|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))))|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)))&(~r1_tmap_1(X52,X49,k2_tmap_1(X50,X49,X51,X52),X55)|r1_tmap_1(X50,X49,X51,X54)|(~r1_tarski(X53,u1_struct_0(X52))|~m1_connsp_2(X53,X50,X54)|X54!=X55)|~m1_subset_1(X55,u1_struct_0(X52))|~m1_subset_1(X54,u1_struct_0(X50))|~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X50)))|(v2_struct_0(X52)|~m1_pre_topc(X52,X50))|(~v1_funct_1(X51)|~v1_funct_2(X51,u1_struct_0(X50),u1_struct_0(X49))|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X50),u1_struct_0(X49)))))|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50))|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.21/0.40  fof(c_0_45, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~l1_pre_topc(X20)|(v2_struct_0(X21)|~m1_pre_topc(X21,X20)|(~m1_subset_1(X22,u1_struct_0(X21))|m1_subset_1(X22,u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.21/0.40  fof(c_0_46, plain, ![X32, X33, X34, X37]:(((m1_subset_1(esk3_3(X32,X33,X34),k1_zfmisc_1(u1_struct_0(X32)))|~r2_hidden(X34,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&((m1_connsp_2(esk3_3(X32,X33,X34),X32,X34)|~r2_hidden(X34,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(r1_tarski(esk3_3(X32,X33,X34),X33)|~r2_hidden(X34,X33)|~m1_subset_1(X34,u1_struct_0(X32))|~v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))))&((m1_subset_1(esk4_2(X32,X33),u1_struct_0(X32))|v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&((r2_hidden(esk4_2(X32,X33),X33)|v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))&(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X32)))|(~m1_connsp_2(X37,X32,esk4_2(X32,X33))|~r1_tarski(X37,X33))|v3_pre_topc(X33,X32)|~m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X32)))|(v2_struct_0(X32)|~v2_pre_topc(X32)|~l1_pre_topc(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_connsp_2])])])])])])).
% 0.21/0.40  cnf(c_0_47, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_38]), c_0_39])).
% 0.21/0.40  cnf(c_0_48, negated_conjecture, (v1_tsep_1(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_49, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.21/0.40  cnf(c_0_50, negated_conjecture, (r2_hidden(esk9_0,esk2_2(esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_35]), c_0_36]), c_0_34])]), c_0_37])).
% 0.21/0.40  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.21/0.40  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk2_2(esk8_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk8_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_42]), c_0_35]), c_0_36]), c_0_34])]), c_0_37])).
% 0.21/0.40  cnf(c_0_53, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.40  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.21/0.40  cnf(c_0_55, plain, (m1_connsp_2(esk3_3(X1,X2,X3),X1,X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.40  cnf(c_0_56, negated_conjecture, (v3_pre_topc(u1_struct_0(esk8_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_25]), c_0_26]), c_0_28])])).
% 0.21/0.40  cnf(c_0_57, negated_conjecture, (m1_subset_1(u1_struct_0(esk8_0),k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_25]), c_0_26])])).
% 0.21/0.40  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_59, negated_conjecture, (r2_hidden(esk9_0,X1)|~r1_tarski(esk2_2(esk8_0,esk9_0),X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.21/0.40  cnf(c_0_60, negated_conjecture, (r1_tarski(esk2_2(esk8_0,esk9_0),u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.40  fof(c_0_61, plain, ![X43, X44, X45, X46, X47, X48]:(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(~v1_funct_1(X45)|~v1_funct_2(X45,u1_struct_0(X44),u1_struct_0(X43))|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X44),u1_struct_0(X43))))|(v2_struct_0(X46)|~m1_pre_topc(X46,X44)|(~m1_subset_1(X47,u1_struct_0(X44))|(~m1_subset_1(X48,u1_struct_0(X46))|(X47!=X48|~r1_tmap_1(X44,X43,X45,X47)|r1_tmap_1(X46,X43,k2_tmap_1(X44,X43,X45,X46),X48)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.21/0.40  cnf(c_0_62, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))|~r1_tarski(X6,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_53, c_0_32])]), c_0_54])).
% 0.21/0.40  cnf(c_0_63, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(esk6_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_64, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_65, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_66, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_69, negated_conjecture, (m1_connsp_2(esk3_3(esk6_0,u1_struct_0(esk8_0),X1),esk6_0,X1)|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_26]), c_0_28]), c_0_57])]), c_0_58])).
% 0.21/0.40  cnf(c_0_70, negated_conjecture, (r2_hidden(esk9_0,u1_struct_0(esk8_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.21/0.40  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_72, plain, (r1_tarski(esk3_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.40  cnf(c_0_73, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.40  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk7_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X2),X1)|~m1_connsp_2(X3,esk6_0,X1)|~m1_pre_topc(X2,esk6_0)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_tarski(X3,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64]), c_0_26]), c_0_65]), c_0_28]), c_0_66]), c_0_67])]), c_0_68]), c_0_58])).
% 0.21/0.40  cnf(c_0_75, negated_conjecture, (m1_connsp_2(esk3_3(esk6_0,u1_struct_0(esk8_0),esk9_0),esk6_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71])])).
% 0.21/0.40  cnf(c_0_76, negated_conjecture, (r1_tarski(esk3_3(esk6_0,u1_struct_0(esk8_0),X1),u1_struct_0(esk8_0))|~m1_subset_1(X1,u1_struct_0(esk6_0))|~r2_hidden(X1,u1_struct_0(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_56]), c_0_26]), c_0_28]), c_0_57])]), c_0_58])).
% 0.21/0.40  cnf(c_0_77, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)|r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_78, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_54])).
% 0.21/0.40  cnf(c_0_79, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)|v2_struct_0(X1)|~r1_tmap_1(X1,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X1),esk9_0)|~m1_pre_topc(X1,esk6_0)|~m1_subset_1(esk9_0,u1_struct_0(X1))|~r1_tarski(esk3_3(esk6_0,u1_struct_0(esk8_0),esk9_0),u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.21/0.40  cnf(c_0_80, negated_conjecture, (r1_tarski(esk3_3(esk6_0,u1_struct_0(esk8_0),esk9_0),u1_struct_0(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_70]), c_0_71])])).
% 0.21/0.40  cnf(c_0_81, negated_conjecture, (r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk9_0)|r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_77, c_0_23])).
% 0.21/0.40  cnf(c_0_82, negated_conjecture, (~r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)|~r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.40  cnf(c_0_83, negated_conjecture, (r1_tmap_1(X1,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk6_0,esk5_0,esk7_0,X2)|~m1_pre_topc(X1,esk6_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_63]), c_0_64]), c_0_26]), c_0_65]), c_0_28]), c_0_66]), c_0_67])]), c_0_68]), c_0_58])).
% 0.21/0.40  cnf(c_0_84, negated_conjecture, (r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_25]), c_0_34])]), c_0_37]), c_0_81])).
% 0.21/0.40  cnf(c_0_85, negated_conjecture, (~r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk9_0)|~r1_tmap_1(esk6_0,esk5_0,esk7_0,esk9_0)), inference(rw,[status(thm)],[c_0_82, c_0_23])).
% 0.21/0.40  cnf(c_0_86, negated_conjecture, (r1_tmap_1(X1,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,X1),esk9_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk6_0)|~m1_subset_1(esk9_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.21/0.40  cnf(c_0_87, negated_conjecture, (~r1_tmap_1(esk8_0,esk5_0,k2_tmap_1(esk6_0,esk5_0,esk7_0,esk8_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_84])])).
% 0.21/0.40  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_25]), c_0_34])]), c_0_87]), c_0_37]), ['proof']).
% 0.21/0.40  # SZS output end CNFRefutation
% 0.21/0.40  # Proof object total steps             : 89
% 0.21/0.40  # Proof object clause steps            : 60
% 0.21/0.40  # Proof object formula steps           : 29
% 0.21/0.40  # Proof object conjectures             : 44
% 0.21/0.40  # Proof object clause conjectures      : 41
% 0.21/0.40  # Proof object formula conjectures     : 3
% 0.21/0.40  # Proof object initial clauses used    : 31
% 0.21/0.40  # Proof object initial formulas used   : 14
% 0.21/0.40  # Proof object generating inferences   : 20
% 0.21/0.40  # Proof object simplifying inferences  : 80
% 0.21/0.40  # Training examples: 0 positive, 0 negative
% 0.21/0.40  # Parsed axioms                        : 14
% 0.21/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.40  # Initial clauses                      : 41
% 0.21/0.40  # Removed in clause preprocessing      : 1
% 0.21/0.40  # Initial clauses in saturation        : 40
% 0.21/0.40  # Processed clauses                    : 205
% 0.21/0.40  # ...of these trivial                  : 0
% 0.21/0.40  # ...subsumed                          : 22
% 0.21/0.40  # ...remaining for further processing  : 183
% 0.21/0.40  # Other redundant clauses eliminated   : 5
% 0.21/0.40  # Clauses deleted for lack of memory   : 0
% 0.21/0.40  # Backward-subsumed                    : 2
% 0.21/0.40  # Backward-rewritten                   : 9
% 0.21/0.40  # Generated clauses                    : 192
% 0.21/0.40  # ...of the previous two non-trivial   : 167
% 0.21/0.40  # Contextual simplify-reflections      : 11
% 0.21/0.40  # Paramodulations                      : 187
% 0.21/0.40  # Factorizations                       : 0
% 0.21/0.40  # Equation resolutions                 : 5
% 0.21/0.40  # Propositional unsat checks           : 0
% 0.21/0.40  #    Propositional check models        : 0
% 0.21/0.40  #    Propositional check unsatisfiable : 0
% 0.21/0.40  #    Propositional clauses             : 0
% 0.21/0.40  #    Propositional clauses after purity: 0
% 0.21/0.40  #    Propositional unsat core size     : 0
% 0.21/0.40  #    Propositional preprocessing time  : 0.000
% 0.21/0.40  #    Propositional encoding time       : 0.000
% 0.21/0.40  #    Propositional solver time         : 0.000
% 0.21/0.40  #    Success case prop preproc time    : 0.000
% 0.21/0.40  #    Success case prop encoding time   : 0.000
% 0.21/0.40  #    Success case prop solver time     : 0.000
% 0.21/0.40  # Current number of processed clauses  : 128
% 0.21/0.40  #    Positive orientable unit clauses  : 39
% 0.21/0.40  #    Positive unorientable unit clauses: 0
% 0.21/0.40  #    Negative unit clauses             : 4
% 0.21/0.40  #    Non-unit-clauses                  : 85
% 0.21/0.40  # Current number of unprocessed clauses: 40
% 0.21/0.40  # ...number of literals in the above   : 117
% 0.21/0.40  # Current number of archived formulas  : 0
% 0.21/0.40  # Current number of archived clauses   : 50
% 0.21/0.40  # Clause-clause subsumption calls (NU) : 2934
% 0.21/0.40  # Rec. Clause-clause subsumption calls : 770
% 0.21/0.40  # Non-unit clause-clause subsumptions  : 35
% 0.21/0.40  # Unit Clause-clause subsumption calls : 66
% 0.21/0.40  # Rewrite failures with RHS unbound    : 0
% 0.21/0.40  # BW rewrite match attempts            : 23
% 0.21/0.40  # BW rewrite match successes           : 2
% 0.21/0.40  # Condensation attempts                : 0
% 0.21/0.40  # Condensation successes               : 0
% 0.21/0.40  # Termbank termtop insertions          : 9769
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.047 s
% 0.21/0.40  # System time              : 0.003 s
% 0.21/0.40  # Total time               : 0.050 s
% 0.21/0.40  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
