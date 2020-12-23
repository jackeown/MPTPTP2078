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
% DateTime   : Thu Dec  3 11:17:30 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   89 (1211 expanded)
%              Number of clauses        :   60 ( 416 expanded)
%              Number of leaves         :   14 ( 293 expanded)
%              Depth                    :   13
%              Number of atoms          :  529 (13093 expanded)
%              Number of equality atoms :   17 ( 684 expanded)
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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))
    & ~ v2_struct_0(esk7_0)
    & v1_tsep_1(esk7_0,esk5_0)
    & m1_pre_topc(esk7_0,esk5_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    & esk8_0 = esk9_0
    & ( ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)
      | ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0) )
    & ( r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)
      | r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_16,plain,(
    ! [X16,X17] :
      ( ~ l1_pre_topc(X16)
      | ~ m1_pre_topc(X17,X16)
      | l1_pre_topc(X17) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,plain,(
    ! [X14,X15] :
      ( ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | v2_pre_topc(X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X36,X37,X38] :
      ( ( ~ v1_tsep_1(X37,X36)
        | ~ m1_pre_topc(X37,X36)
        | v3_pre_topc(X38,X36)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( v1_tsep_1(X37,X36)
        | ~ v3_pre_topc(X38,X36)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( m1_pre_topc(X37,X36)
        | ~ v3_pre_topc(X38,X36)
        | X38 != u1_struct_0(X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_19,plain,(
    ! [X27,X28,X29] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
      | ~ m1_subset_1(X29,u1_struct_0(X27))
      | ~ m1_connsp_2(X28,X27,X29)
      | r2_hidden(X29,X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_20,plain,(
    ! [X21,X22,X23] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | ~ m1_connsp_2(X23,X21,X22)
      | m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_21,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,u1_struct_0(X24))
      | m1_connsp_2(esk1_2(X24,X25),X24,X25) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
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
    ! [X39,X40] :
      ( ~ l1_pre_topc(X39)
      | ~ m1_pre_topc(X40,X39)
      | m1_subset_1(u1_struct_0(X40),k1_zfmisc_1(u1_struct_0(X39))) ) ),
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
    | m1_connsp_2(esk1_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_36,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_26]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_38,plain,(
    ! [X30,X31,X32,X35] :
      ( ( m1_subset_1(esk2_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_connsp_2(esk2_3(X30,X31,X32),X30,X32)
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( r1_tarski(esk2_3(X30,X31,X32),X31)
        | ~ r2_hidden(X32,X31)
        | ~ m1_subset_1(X32,u1_struct_0(X30))
        | ~ v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk3_2(X30,X31),u1_struct_0(X30))
        | v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( r2_hidden(esk3_2(X30,X31),X31)
        | v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ m1_connsp_2(X35,X30,esk3_2(X30,X31))
        | ~ r1_tarski(X35,X31)
        | v3_pre_topc(X31,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | v2_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_connsp_2])])])])])])).

fof(c_0_39,plain,(
    ! [X11,X12,X13] :
      ( ~ r2_hidden(X11,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X13))
      | m1_subset_1(X11,X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_40,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | ~ r2_hidden(X10,X9)
      | r2_hidden(X10,X8) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_43,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( m1_connsp_2(esk1_2(esk7_0,esk8_0),esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])]),c_0_37])).

fof(c_0_45,plain,(
    ! [X47,X48,X49,X50,X51,X52,X53] :
      ( ( ~ r1_tmap_1(X48,X47,X49,X52)
        | r1_tmap_1(X50,X47,k2_tmap_1(X48,X47,X49,X50),X53)
        | ~ r1_tarski(X51,u1_struct_0(X50))
        | ~ m1_connsp_2(X51,X48,X52)
        | X52 != X53
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X48))
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X48),u1_struct_0(X47))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) )
      & ( ~ r1_tmap_1(X50,X47,k2_tmap_1(X48,X47,X49,X50),X53)
        | r1_tmap_1(X48,X47,X49,X52)
        | ~ r1_tarski(X51,u1_struct_0(X50))
        | ~ m1_connsp_2(X51,X48,X52)
        | X52 != X53
        | ~ m1_subset_1(X53,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X48))
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X48)))
        | v2_struct_0(X50)
        | ~ m1_pre_topc(X50,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X48),u1_struct_0(X47))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47))))
        | v2_struct_0(X48)
        | ~ v2_pre_topc(X48)
        | ~ l1_pre_topc(X48)
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

fof(c_0_46,plain,(
    ! [X18,X19,X20] :
      ( v2_struct_0(X18)
      | ~ l1_pre_topc(X18)
      | v2_struct_0(X19)
      | ~ m1_pre_topc(X19,X18)
      | ~ m1_subset_1(X20,u1_struct_0(X19))
      | m1_subset_1(X20,u1_struct_0(X18)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_47,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_41])).

cnf(c_0_50,negated_conjecture,
    ( v1_tsep_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_2(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_35]),c_0_36]),c_0_34])]),c_0_37])).

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
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_25]),c_0_26]),c_0_28])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_25]),c_0_26])])).

cnf(c_0_58,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk8_0,X1)
    | ~ m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_44]),c_0_35]),c_0_36]),c_0_34])]),c_0_37])).

cnf(c_0_61,plain,
    ( m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_62,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X41))
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))
      | v2_struct_0(X44)
      | ~ m1_pre_topc(X44,X42)
      | ~ m1_subset_1(X45,u1_struct_0(X42))
      | ~ m1_subset_1(X46,u1_struct_0(X44))
      | X45 != X46
      | ~ r1_tmap_1(X42,X41,X43,X45)
      | r1_tmap_1(X44,X41,k2_tmap_1(X42,X41,X43,X44),X46) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_63,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X5)
    | ~ r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(X6,u1_struct_0(X5))
    | ~ m1_connsp_2(X6,X1,X4)
    | ~ m1_pre_topc(X5,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X4,u1_struct_0(X5)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_53,c_0_32])]),c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk2_3(esk5_0,u1_struct_0(esk7_0),X1),u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_26]),c_0_28]),c_0_57])]),c_0_58])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_72,plain,
    ( m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_61,c_0_48])).

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
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_74,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X2),X1)
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ m1_connsp_2(X3,esk5_0,X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_26]),c_0_66]),c_0_28]),c_0_67]),c_0_68])]),c_0_69]),c_0_58])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,negated_conjecture,
    ( m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),X1),esk5_0,X1)
    | ~ r2_hidden(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_56]),c_0_26]),c_0_28]),c_0_57])]),c_0_58])).

cnf(c_0_77,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)
    | r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0) ),
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
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)
    | ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),X1)
    | ~ m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_25])]),c_0_37])).

cnf(c_0_80,negated_conjecture,
    ( m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_71])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)
    | r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_77,c_0_23])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)
    | ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_64]),c_0_65]),c_0_26]),c_0_66]),c_0_28]),c_0_67]),c_0_68])]),c_0_69]),c_0_58])).

cnf(c_0_84,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_34])]),c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_82,c_0_23])).

cnf(c_0_86,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_87,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_84])])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_25]),c_0_34])]),c_0_87]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:15:27 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.37  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.18/0.37  # and selection function SelectCQIPrecWNTNp.
% 0.18/0.37  #
% 0.18/0.37  # Preprocessing time       : 0.029 s
% 0.18/0.37  # Presaturation interreduction done
% 0.18/0.37  
% 0.18/0.37  # Proof found!
% 0.18/0.37  # SZS status Theorem
% 0.18/0.37  # SZS output start CNFRefutation
% 0.18/0.37  fof(t67_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.18/0.37  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.18/0.37  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.18/0.37  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.18/0.37  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.18/0.37  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.18/0.37  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.18/0.37  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.18/0.37  fof(t9_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.18/0.37  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.18/0.37  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.18/0.37  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.18/0.37  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.18/0.37  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.18/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))))), inference(assume_negation,[status(cth)],[t67_tmap_1])).
% 0.18/0.37  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(((~v2_struct_0(esk7_0)&v1_tsep_1(esk7_0,esk5_0))&m1_pre_topc(esk7_0,esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(esk8_0=esk9_0&((~r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0))&(r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.18/0.37  fof(c_0_16, plain, ![X16, X17]:(~l1_pre_topc(X16)|(~m1_pre_topc(X17,X16)|l1_pre_topc(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.18/0.37  fof(c_0_17, plain, ![X14, X15]:(~v2_pre_topc(X14)|~l1_pre_topc(X14)|(~m1_pre_topc(X15,X14)|v2_pre_topc(X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.18/0.37  fof(c_0_18, plain, ![X36, X37, X38]:((~v1_tsep_1(X37,X36)|~m1_pre_topc(X37,X36)|v3_pre_topc(X38,X36)|X38!=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&((v1_tsep_1(X37,X36)|~v3_pre_topc(X38,X36)|X38!=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(m1_pre_topc(X37,X36)|~v3_pre_topc(X38,X36)|X38!=u1_struct_0(X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.18/0.37  fof(c_0_19, plain, ![X27, X28, X29]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|(~m1_subset_1(X29,u1_struct_0(X27))|(~m1_connsp_2(X28,X27,X29)|r2_hidden(X29,X28))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.18/0.37  fof(c_0_20, plain, ![X21, X22, X23]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|~m1_subset_1(X22,u1_struct_0(X21))|(~m1_connsp_2(X23,X21,X22)|m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X21))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.18/0.37  fof(c_0_21, plain, ![X24, X25]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|~m1_subset_1(X25,u1_struct_0(X24))|m1_connsp_2(esk1_2(X24,X25),X24,X25)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.18/0.37  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_23, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.37  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_27, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.37  cnf(c_0_28, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_29, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.37  fof(c_0_30, plain, ![X39, X40]:(~l1_pre_topc(X39)|(~m1_pre_topc(X40,X39)|m1_subset_1(u1_struct_0(X40),k1_zfmisc_1(u1_struct_0(X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.18/0.37  cnf(c_0_31, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.37  cnf(c_0_32, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.18/0.37  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_connsp_2(esk1_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.18/0.37  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.18/0.37  cnf(c_0_35, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.18/0.37  cnf(c_0_36, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_25]), c_0_26]), c_0_28])])).
% 0.18/0.37  cnf(c_0_37, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  fof(c_0_38, plain, ![X30, X31, X32, X35]:(((m1_subset_1(esk2_3(X30,X31,X32),k1_zfmisc_1(u1_struct_0(X30)))|~r2_hidden(X32,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~v3_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&((m1_connsp_2(esk2_3(X30,X31,X32),X30,X32)|~r2_hidden(X32,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~v3_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(r1_tarski(esk2_3(X30,X31,X32),X31)|~r2_hidden(X32,X31)|~m1_subset_1(X32,u1_struct_0(X30))|~v3_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))))&((m1_subset_1(esk3_2(X30,X31),u1_struct_0(X30))|v3_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&((r2_hidden(esk3_2(X30,X31),X31)|v3_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))&(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X30)))|(~m1_connsp_2(X35,X30,esk3_2(X30,X31))|~r1_tarski(X35,X31))|v3_pre_topc(X31,X30)|~m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))|(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_connsp_2])])])])])])).
% 0.18/0.37  fof(c_0_39, plain, ![X11, X12, X13]:(~r2_hidden(X11,X12)|~m1_subset_1(X12,k1_zfmisc_1(X13))|m1_subset_1(X11,X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.18/0.37  cnf(c_0_40, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_29])).
% 0.18/0.37  cnf(c_0_41, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.18/0.37  fof(c_0_42, plain, ![X8, X9, X10]:(~m1_subset_1(X9,k1_zfmisc_1(X8))|(~r2_hidden(X10,X9)|r2_hidden(X10,X8))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.18/0.37  cnf(c_0_43, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_31, c_0_32])).
% 0.18/0.37  cnf(c_0_44, negated_conjecture, (m1_connsp_2(esk1_2(esk7_0,esk8_0),esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])]), c_0_37])).
% 0.18/0.37  fof(c_0_45, plain, ![X47, X48, X49, X50, X51, X52, X53]:((~r1_tmap_1(X48,X47,X49,X52)|r1_tmap_1(X50,X47,k2_tmap_1(X48,X47,X49,X50),X53)|(~r1_tarski(X51,u1_struct_0(X50))|~m1_connsp_2(X51,X48,X52)|X52!=X53)|~m1_subset_1(X53,u1_struct_0(X50))|~m1_subset_1(X52,u1_struct_0(X48))|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X48)))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48))|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X48),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47)))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))&(~r1_tmap_1(X50,X47,k2_tmap_1(X48,X47,X49,X50),X53)|r1_tmap_1(X48,X47,X49,X52)|(~r1_tarski(X51,u1_struct_0(X50))|~m1_connsp_2(X51,X48,X52)|X52!=X53)|~m1_subset_1(X53,u1_struct_0(X50))|~m1_subset_1(X52,u1_struct_0(X48))|~m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X48)))|(v2_struct_0(X50)|~m1_pre_topc(X50,X48))|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X48),u1_struct_0(X47))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X48),u1_struct_0(X47)))))|(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.18/0.37  fof(c_0_46, plain, ![X18, X19, X20]:(v2_struct_0(X18)|~l1_pre_topc(X18)|(v2_struct_0(X19)|~m1_pre_topc(X19,X18)|(~m1_subset_1(X20,u1_struct_0(X19))|m1_subset_1(X20,u1_struct_0(X18))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.18/0.37  cnf(c_0_47, plain, (r1_tarski(esk2_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.37  cnf(c_0_48, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.18/0.37  cnf(c_0_49, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_41])).
% 0.18/0.37  cnf(c_0_50, negated_conjecture, (v1_tsep_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_51, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.37  cnf(c_0_52, negated_conjecture, (r2_hidden(esk8_0,esk1_2(esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_35]), c_0_36]), c_0_34])]), c_0_37])).
% 0.18/0.37  cnf(c_0_53, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.37  cnf(c_0_54, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.18/0.37  cnf(c_0_55, plain, (r1_tarski(esk2_3(X1,X2,X3),X2)|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_47, c_0_48])).
% 0.18/0.37  cnf(c_0_56, negated_conjecture, (v3_pre_topc(u1_struct_0(esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_25]), c_0_26]), c_0_28])])).
% 0.18/0.37  cnf(c_0_57, negated_conjecture, (m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_25]), c_0_26])])).
% 0.18/0.37  cnf(c_0_58, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_59, negated_conjecture, (r2_hidden(esk8_0,X1)|~m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.18/0.37  cnf(c_0_60, negated_conjecture, (m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_44]), c_0_35]), c_0_36]), c_0_34])]), c_0_37])).
% 0.18/0.37  cnf(c_0_61, plain, (m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.18/0.37  fof(c_0_62, plain, ![X41, X42, X43, X44, X45, X46]:(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(v2_struct_0(X42)|~v2_pre_topc(X42)|~l1_pre_topc(X42)|(~v1_funct_1(X43)|~v1_funct_2(X43,u1_struct_0(X42),u1_struct_0(X41))|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X41))))|(v2_struct_0(X44)|~m1_pre_topc(X44,X42)|(~m1_subset_1(X45,u1_struct_0(X42))|(~m1_subset_1(X46,u1_struct_0(X44))|(X45!=X46|~r1_tmap_1(X42,X41,X43,X45)|r1_tmap_1(X44,X41,k2_tmap_1(X42,X41,X43,X44),X46)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.18/0.37  cnf(c_0_63, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~r1_tarski(X6,u1_struct_0(X5))|~m1_connsp_2(X6,X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_53, c_0_32])]), c_0_54])).
% 0.18/0.37  cnf(c_0_64, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_65, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_66, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_67, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_69, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_70, negated_conjecture, (r1_tarski(esk2_3(esk5_0,u1_struct_0(esk7_0),X1),u1_struct_0(esk7_0))|~r2_hidden(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_26]), c_0_28]), c_0_57])]), c_0_58])).
% 0.18/0.37  cnf(c_0_71, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.18/0.37  cnf(c_0_72, plain, (m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)|v2_struct_0(X1)|~v3_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[c_0_61, c_0_48])).
% 0.18/0.37  cnf(c_0_73, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.37  cnf(c_0_74, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X2),X1)|~r1_tarski(X3,u1_struct_0(X2))|~m1_connsp_2(X3,esk5_0,X1)|~m1_pre_topc(X2,esk5_0)|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_26]), c_0_66]), c_0_28]), c_0_67]), c_0_68])]), c_0_69]), c_0_58])).
% 0.18/0.37  cnf(c_0_75, negated_conjecture, (r1_tarski(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.18/0.37  cnf(c_0_76, negated_conjecture, (m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),X1),esk5_0,X1)|~r2_hidden(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_56]), c_0_26]), c_0_28]), c_0_57])]), c_0_58])).
% 0.18/0.37  cnf(c_0_77, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_78, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_54])).
% 0.18/0.37  cnf(c_0_79, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)|~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),X1)|~m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_25])]), c_0_37])).
% 0.18/0.37  cnf(c_0_80, negated_conjecture, (m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,esk8_0)), inference(spm,[status(thm)],[c_0_76, c_0_71])).
% 0.18/0.37  cnf(c_0_81, negated_conjecture, (r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)|r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_77, c_0_23])).
% 0.18/0.37  cnf(c_0_82, negated_conjecture, (~r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.37  cnf(c_0_83, negated_conjecture, (r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk5_0,esk4_0,esk6_0,X2)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_64]), c_0_65]), c_0_26]), c_0_66]), c_0_28]), c_0_67]), c_0_68])]), c_0_69]), c_0_58])).
% 0.18/0.37  cnf(c_0_84, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_34])]), c_0_81])).
% 0.18/0.37  cnf(c_0_85, negated_conjecture, (~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)|~r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_82, c_0_23])).
% 0.18/0.37  cnf(c_0_86, negated_conjecture, (r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),esk8_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.18/0.37  cnf(c_0_87, negated_conjecture, (~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_84])])).
% 0.18/0.37  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_25]), c_0_34])]), c_0_87]), c_0_37]), ['proof']).
% 0.18/0.37  # SZS output end CNFRefutation
% 0.18/0.37  # Proof object total steps             : 89
% 0.18/0.37  # Proof object clause steps            : 60
% 0.18/0.37  # Proof object formula steps           : 29
% 0.18/0.37  # Proof object conjectures             : 42
% 0.18/0.37  # Proof object clause conjectures      : 39
% 0.18/0.37  # Proof object formula conjectures     : 3
% 0.18/0.37  # Proof object initial clauses used    : 30
% 0.18/0.37  # Proof object initial formulas used   : 14
% 0.18/0.37  # Proof object generating inferences   : 19
% 0.18/0.37  # Proof object simplifying inferences  : 79
% 0.18/0.37  # Training examples: 0 positive, 0 negative
% 0.18/0.37  # Parsed axioms                        : 14
% 0.18/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.37  # Initial clauses                      : 38
% 0.18/0.37  # Removed in clause preprocessing      : 1
% 0.18/0.37  # Initial clauses in saturation        : 37
% 0.18/0.37  # Processed clauses                    : 155
% 0.18/0.37  # ...of these trivial                  : 0
% 0.18/0.37  # ...subsumed                          : 7
% 0.18/0.37  # ...remaining for further processing  : 148
% 0.18/0.37  # Other redundant clauses eliminated   : 5
% 0.18/0.37  # Clauses deleted for lack of memory   : 0
% 0.18/0.37  # Backward-subsumed                    : 0
% 0.18/0.37  # Backward-rewritten                   : 2
% 0.18/0.37  # Generated clauses                    : 105
% 0.18/0.37  # ...of the previous two non-trivial   : 94
% 0.18/0.37  # Contextual simplify-reflections      : 14
% 0.18/0.37  # Paramodulations                      : 100
% 0.18/0.37  # Factorizations                       : 0
% 0.18/0.37  # Equation resolutions                 : 5
% 0.18/0.37  # Propositional unsat checks           : 0
% 0.18/0.37  #    Propositional check models        : 0
% 0.18/0.37  #    Propositional check unsatisfiable : 0
% 0.18/0.37  #    Propositional clauses             : 0
% 0.18/0.37  #    Propositional clauses after purity: 0
% 0.18/0.37  #    Propositional unsat core size     : 0
% 0.18/0.37  #    Propositional preprocessing time  : 0.000
% 0.18/0.37  #    Propositional encoding time       : 0.000
% 0.18/0.37  #    Propositional solver time         : 0.000
% 0.18/0.37  #    Success case prop preproc time    : 0.000
% 0.18/0.37  #    Success case prop encoding time   : 0.000
% 0.18/0.37  #    Success case prop solver time     : 0.000
% 0.18/0.37  # Current number of processed clauses  : 105
% 0.18/0.37  #    Positive orientable unit clauses  : 29
% 0.18/0.37  #    Positive unorientable unit clauses: 0
% 0.18/0.37  #    Negative unit clauses             : 4
% 0.18/0.37  #    Non-unit-clauses                  : 72
% 0.18/0.37  # Current number of unprocessed clauses: 12
% 0.18/0.37  # ...number of literals in the above   : 40
% 0.18/0.37  # Current number of archived formulas  : 0
% 0.18/0.37  # Current number of archived clauses   : 38
% 0.18/0.37  # Clause-clause subsumption calls (NU) : 1442
% 0.18/0.37  # Rec. Clause-clause subsumption calls : 341
% 0.18/0.37  # Non-unit clause-clause subsumptions  : 21
% 0.18/0.37  # Unit Clause-clause subsumption calls : 25
% 0.18/0.37  # Rewrite failures with RHS unbound    : 0
% 0.18/0.37  # BW rewrite match attempts            : 6
% 0.18/0.37  # BW rewrite match successes           : 1
% 0.18/0.37  # Condensation attempts                : 0
% 0.18/0.37  # Condensation successes               : 0
% 0.18/0.37  # Termbank termtop insertions          : 8029
% 0.18/0.37  
% 0.18/0.37  # -------------------------------------------------
% 0.18/0.37  # User time                : 0.038 s
% 0.18/0.37  # System time              : 0.007 s
% 0.18/0.37  # Total time               : 0.045 s
% 0.18/0.37  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
