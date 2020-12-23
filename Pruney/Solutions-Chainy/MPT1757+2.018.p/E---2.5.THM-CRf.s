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
% DateTime   : Thu Dec  3 11:17:31 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 (1267 expanded)
%              Number of clauses        :   61 ( 436 expanded)
%              Number of leaves         :   14 ( 305 expanded)
%              Depth                    :   15
%              Number of atoms          :  529 (13749 expanded)
%              Number of equality atoms :   17 ( 724 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

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

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

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
    ! [X15,X16] :
      ( ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X15)
      | l1_pre_topc(X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,plain,(
    ! [X13,X14] :
      ( ~ v2_pre_topc(X13)
      | ~ l1_pre_topc(X13)
      | ~ m1_pre_topc(X14,X13)
      | v2_pre_topc(X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_18,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ v2_pre_topc(X26)
      | ~ l1_pre_topc(X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | ~ m1_connsp_2(X27,X26,X28)
      | r2_hidden(X28,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).

fof(c_0_19,plain,(
    ! [X20,X21,X22] :
      ( v2_struct_0(X20)
      | ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,u1_struct_0(X20))
      | ~ m1_connsp_2(X22,X20,X21)
      | m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_20,plain,(
    ! [X23,X24] :
      ( v2_struct_0(X23)
      | ~ v2_pre_topc(X23)
      | ~ l1_pre_topc(X23)
      | ~ m1_subset_1(X24,u1_struct_0(X23))
      | m1_connsp_2(esk1_2(X23,X24),X23,X24) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( esk8_0 = esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_connsp_2(X2,X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk1_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_25]),c_0_27])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_35,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,X3)
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( m1_connsp_2(esk1_2(esk7_0,esk8_0),esk7_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

fof(c_0_38,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_39,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_2(esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_32]),c_0_33]),c_0_31])]),c_0_34])).

fof(c_0_41,plain,(
    ! [X35,X36,X37] :
      ( ( ~ v1_tsep_1(X36,X35)
        | ~ m1_pre_topc(X36,X35)
        | v3_pre_topc(X37,X35)
        | X37 != u1_struct_0(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( v1_tsep_1(X36,X35)
        | ~ v3_pre_topc(X37,X35)
        | X37 != u1_struct_0(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( m1_pre_topc(X36,X35)
        | ~ v3_pre_topc(X37,X35)
        | X37 != u1_struct_0(X36)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))
        | ~ m1_pre_topc(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_37]),c_0_32]),c_0_33]),c_0_31])]),c_0_34])).

cnf(c_0_45,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_pre_topc(X39,X38)
      | m1_subset_1(u1_struct_0(X39),k1_zfmisc_1(u1_struct_0(X38))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_47,plain,(
    ! [X46,X47,X48,X49,X50,X51,X52] :
      ( ( ~ r1_tmap_1(X47,X46,X48,X51)
        | r1_tmap_1(X49,X46,k2_tmap_1(X47,X46,X48,X49),X52)
        | ~ r1_tarski(X50,u1_struct_0(X49))
        | ~ m1_connsp_2(X50,X47,X51)
        | X51 != X52
        | ~ m1_subset_1(X52,u1_struct_0(X49))
        | ~ m1_subset_1(X51,u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X47)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X47),u1_struct_0(X46))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) )
      & ( ~ r1_tmap_1(X49,X46,k2_tmap_1(X47,X46,X48,X49),X52)
        | r1_tmap_1(X47,X46,X48,X51)
        | ~ r1_tarski(X50,u1_struct_0(X49))
        | ~ m1_connsp_2(X50,X47,X51)
        | X51 != X52
        | ~ m1_subset_1(X52,u1_struct_0(X49))
        | ~ m1_subset_1(X51,u1_struct_0(X47))
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))
        | v2_struct_0(X49)
        | ~ m1_pre_topc(X49,X47)
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X47),u1_struct_0(X46))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46))))
        | v2_struct_0(X47)
        | ~ v2_pre_topc(X47)
        | ~ l1_pre_topc(X47)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

fof(c_0_48,plain,(
    ! [X17,X18,X19] :
      ( v2_struct_0(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(X18)
      | ~ m1_pre_topc(X18,X17)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | m1_subset_1(X19,u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_49,plain,(
    ! [X29,X30,X31,X34] :
      ( ( m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r2_hidden(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_connsp_2(esk2_3(X29,X30,X31),X29,X31)
        | ~ r2_hidden(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( r1_tarski(esk2_3(X29,X30,X31),X30)
        | ~ r2_hidden(X31,X30)
        | ~ m1_subset_1(X31,u1_struct_0(X29))
        | ~ v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( m1_subset_1(esk3_2(X29,X30),u1_struct_0(X29))
        | v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( r2_hidden(esk3_2(X29,X30),X30)
        | v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) )
      & ( ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_connsp_2(X34,X29,esk3_2(X29,X30))
        | ~ r1_tarski(X34,X30)
        | v3_pre_topc(X30,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_connsp_2])])])])])])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_31])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_52,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_55,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_56,plain,
    ( r1_tarski(esk2_3(X1,X2,X3),X2)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( v1_tsep_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_60,plain,(
    ! [X40,X41,X42,X43,X44,X45] :
      ( v2_struct_0(X40)
      | ~ v2_pre_topc(X40)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X41)
      | ~ v2_pre_topc(X41)
      | ~ l1_pre_topc(X41)
      | ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,u1_struct_0(X41),u1_struct_0(X40))
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))
      | v2_struct_0(X43)
      | ~ m1_pre_topc(X43,X41)
      | ~ m1_subset_1(X44,u1_struct_0(X41))
      | ~ m1_subset_1(X45,u1_struct_0(X43))
      | X44 != X45
      | ~ r1_tmap_1(X41,X40,X42,X44)
      | r1_tmap_1(X43,X40,k2_tmap_1(X41,X40,X42,X43),X45) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_61,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_54,c_0_29])]),c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_67,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_68,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_69,negated_conjecture,
    ( r1_tarski(esk2_3(X1,u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(esk7_0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_70,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_24]),c_0_25]),c_0_27])])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_24]),c_0_25])])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_73,plain,
    ( m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_74,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X2),X1)
    | ~ r1_tarski(X3,u1_struct_0(X2))
    | ~ m1_connsp_2(X3,esk5_0,X1)
    | ~ m1_pre_topc(X2,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63]),c_0_25]),c_0_64]),c_0_27]),c_0_65]),c_0_66])]),c_0_67]),c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_25]),c_0_27]),c_0_71]),c_0_72])]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( m1_connsp_2(esk2_3(X1,u1_struct_0(esk7_0),esk8_0),X1,esk8_0)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(esk7_0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_57])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)
    | r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_79,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]),c_0_55])).

cnf(c_0_80,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)
    | ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),X1)
    | ~ m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_24])]),c_0_34])).

cnf(c_0_81,negated_conjecture,
    ( m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_70]),c_0_25]),c_0_27]),c_0_71]),c_0_72])]),c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)
    | r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_22])).

cnf(c_0_83,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)
    | ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_84,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_62]),c_0_63]),c_0_25]),c_0_64]),c_0_27]),c_0_65]),c_0_66])]),c_0_67]),c_0_68])).

cnf(c_0_85,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_31])]),c_0_82])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)
    | ~ r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_83,c_0_22])).

cnf(c_0_87,negated_conjecture,
    ( r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),esk8_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_85])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_24]),c_0_31])]),c_0_88]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.21/0.39  # and selection function SelectCQIPrecWNTNp.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.029 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t67_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.21/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.21/0.39  fof(t6_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(m1_connsp_2(X2,X1,X3)=>r2_hidden(X3,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_connsp_2)).
% 0.21/0.39  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.21/0.39  fof(existence_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>?[X3]:m1_connsp_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 0.21/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.21/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.39  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.21/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.39  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.21/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.21/0.39  fof(t9_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((m1_connsp_2(X4,X1,X3)&r1_tarski(X4,X2)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_connsp_2)).
% 0.21/0.39  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.21/0.39  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))))), inference(assume_negation,[status(cth)],[t67_tmap_1])).
% 0.21/0.39  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0)))))&(((~v2_struct_0(esk7_0)&v1_tsep_1(esk7_0,esk5_0))&m1_pre_topc(esk7_0,esk5_0))&(m1_subset_1(esk8_0,u1_struct_0(esk5_0))&(m1_subset_1(esk9_0,u1_struct_0(esk7_0))&(esk8_0=esk9_0&((~r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0))&(r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.21/0.39  fof(c_0_16, plain, ![X15, X16]:(~l1_pre_topc(X15)|(~m1_pre_topc(X16,X15)|l1_pre_topc(X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.39  fof(c_0_17, plain, ![X13, X14]:(~v2_pre_topc(X13)|~l1_pre_topc(X13)|(~m1_pre_topc(X14,X13)|v2_pre_topc(X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.21/0.39  fof(c_0_18, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))|(~m1_subset_1(X28,u1_struct_0(X26))|(~m1_connsp_2(X27,X26,X28)|r2_hidden(X28,X27))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t6_connsp_2])])])])).
% 0.21/0.39  fof(c_0_19, plain, ![X20, X21, X22]:(v2_struct_0(X20)|~v2_pre_topc(X20)|~l1_pre_topc(X20)|~m1_subset_1(X21,u1_struct_0(X20))|(~m1_connsp_2(X22,X20,X21)|m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.21/0.39  fof(c_0_20, plain, ![X23, X24]:(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)|~m1_subset_1(X24,u1_struct_0(X23))|m1_connsp_2(esk1_2(X23,X24),X23,X24)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (esk8_0=esk9_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_23, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_26, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.39  cnf(c_0_27, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_connsp_2(X2,X1,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.39  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.39  cnf(c_0_30, plain, (v2_struct_0(X1)|m1_connsp_2(esk1_2(X1,X2),X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (v2_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_25]), c_0_27])])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_35, plain, ![X10, X11, X12]:(~r2_hidden(X10,X11)|~m1_subset_1(X11,k1_zfmisc_1(X12))|~v1_xboole_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.21/0.39  cnf(c_0_36, plain, (v2_struct_0(X1)|r2_hidden(X2,X3)|~m1_connsp_2(X3,X1,X2)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_28, c_0_29])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (m1_connsp_2(esk1_2(esk7_0,esk8_0),esk7_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33])]), c_0_34])).
% 0.21/0.39  fof(c_0_38, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.39  cnf(c_0_39, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(esk8_0,esk1_2(esk7_0,esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_32]), c_0_33]), c_0_31])]), c_0_34])).
% 0.21/0.39  fof(c_0_41, plain, ![X35, X36, X37]:((~v1_tsep_1(X36,X35)|~m1_pre_topc(X36,X35)|v3_pre_topc(X37,X35)|X37!=u1_struct_0(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X36,X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&((v1_tsep_1(X36,X35)|~v3_pre_topc(X37,X35)|X37!=u1_struct_0(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X36,X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(m1_pre_topc(X36,X35)|~v3_pre_topc(X37,X35)|X37!=u1_struct_0(X36)|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X35)))|~m1_pre_topc(X36,X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.21/0.39  cnf(c_0_42, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.39  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk1_2(esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_37]), c_0_32]), c_0_33]), c_0_31])]), c_0_34])).
% 0.21/0.39  cnf(c_0_45, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.21/0.39  fof(c_0_46, plain, ![X38, X39]:(~l1_pre_topc(X38)|(~m1_pre_topc(X39,X38)|m1_subset_1(u1_struct_0(X39),k1_zfmisc_1(u1_struct_0(X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.39  fof(c_0_47, plain, ![X46, X47, X48, X49, X50, X51, X52]:((~r1_tmap_1(X47,X46,X48,X51)|r1_tmap_1(X49,X46,k2_tmap_1(X47,X46,X48,X49),X52)|(~r1_tarski(X50,u1_struct_0(X49))|~m1_connsp_2(X50,X47,X51)|X51!=X52)|~m1_subset_1(X52,u1_struct_0(X49))|~m1_subset_1(X51,u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))|(v2_struct_0(X49)|~m1_pre_topc(X49,X47))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X47),u1_struct_0(X46))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46)))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))&(~r1_tmap_1(X49,X46,k2_tmap_1(X47,X46,X48,X49),X52)|r1_tmap_1(X47,X46,X48,X51)|(~r1_tarski(X50,u1_struct_0(X49))|~m1_connsp_2(X50,X47,X51)|X51!=X52)|~m1_subset_1(X52,u1_struct_0(X49))|~m1_subset_1(X51,u1_struct_0(X47))|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))|(v2_struct_0(X49)|~m1_pre_topc(X49,X47))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X47),u1_struct_0(X46))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X46)))))|(v2_struct_0(X47)|~v2_pre_topc(X47)|~l1_pre_topc(X47))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.21/0.39  fof(c_0_48, plain, ![X17, X18, X19]:(v2_struct_0(X17)|~l1_pre_topc(X17)|(v2_struct_0(X18)|~m1_pre_topc(X18,X17)|(~m1_subset_1(X19,u1_struct_0(X18))|m1_subset_1(X19,u1_struct_0(X17))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.21/0.39  fof(c_0_49, plain, ![X29, X30, X31, X34]:(((m1_subset_1(esk2_3(X29,X30,X31),k1_zfmisc_1(u1_struct_0(X29)))|~r2_hidden(X31,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((m1_connsp_2(esk2_3(X29,X30,X31),X29,X31)|~r2_hidden(X31,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(r1_tarski(esk2_3(X29,X30,X31),X30)|~r2_hidden(X31,X30)|~m1_subset_1(X31,u1_struct_0(X29))|~v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))))&((m1_subset_1(esk3_2(X29,X30),u1_struct_0(X29))|v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&((r2_hidden(esk3_2(X29,X30),X30)|v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))&(~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X29)))|(~m1_connsp_2(X34,X29,esk3_2(X29,X30))|~r1_tarski(X34,X30))|v3_pre_topc(X30,X29)|~m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29)))|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t9_connsp_2])])])])])])).
% 0.21/0.39  cnf(c_0_50, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))|v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_31])).
% 0.21/0.39  cnf(c_0_51, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.21/0.39  cnf(c_0_52, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_45])).
% 0.21/0.39  cnf(c_0_53, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.39  cnf(c_0_54, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.39  cnf(c_0_55, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.39  cnf(c_0_56, plain, (r1_tarski(esk2_3(X1,X2,X3),X2)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.39  cnf(c_0_57, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.39  cnf(c_0_58, plain, (v3_pre_topc(u1_struct_0(X1),X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_52]), c_0_53])).
% 0.21/0.39  cnf(c_0_59, negated_conjecture, (v1_tsep_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  fof(c_0_60, plain, ![X40, X41, X42, X43, X44, X45]:(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X41),u1_struct_0(X40))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))|(v2_struct_0(X43)|~m1_pre_topc(X43,X41)|(~m1_subset_1(X44,u1_struct_0(X41))|(~m1_subset_1(X45,u1_struct_0(X43))|(X44!=X45|~r1_tmap_1(X41,X40,X42,X44)|r1_tmap_1(X43,X40,k2_tmap_1(X41,X40,X42,X43),X45)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.21/0.39  cnf(c_0_61, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~r1_tarski(X6,u1_struct_0(X5))|~m1_connsp_2(X6,X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_54, c_0_29])]), c_0_55])).
% 0.21/0.39  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk5_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_63, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_64, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_65, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_66, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_67, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_68, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_69, negated_conjecture, (r1_tarski(esk2_3(X1,u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(esk7_0),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.39  cnf(c_0_70, negated_conjecture, (v3_pre_topc(u1_struct_0(esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_24]), c_0_25]), c_0_27])])).
% 0.21/0.39  cnf(c_0_71, negated_conjecture, (m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_24]), c_0_25])])).
% 0.21/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_73, plain, (m1_connsp_2(esk2_3(X1,X2,X3),X1,X3)|v2_struct_0(X1)|~r2_hidden(X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.39  cnf(c_0_74, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.21/0.39  cnf(c_0_75, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X2),X1)|~r1_tarski(X3,u1_struct_0(X2))|~m1_connsp_2(X3,esk5_0,X1)|~m1_pre_topc(X2,esk5_0)|~m1_subset_1(X1,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63]), c_0_25]), c_0_64]), c_0_27]), c_0_65]), c_0_66])]), c_0_67]), c_0_68])).
% 0.21/0.39  cnf(c_0_76, negated_conjecture, (r1_tarski(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_25]), c_0_27]), c_0_71]), c_0_72])]), c_0_68])).
% 0.21/0.39  cnf(c_0_77, negated_conjecture, (m1_connsp_2(esk2_3(X1,u1_struct_0(esk7_0),esk8_0),X1,esk8_0)|v2_struct_0(X1)|~v3_pre_topc(u1_struct_0(esk7_0),X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_73, c_0_57])).
% 0.21/0.39  cnf(c_0_78, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_79, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_74]), c_0_55])).
% 0.21/0.39  cnf(c_0_80, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,X1)|~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),X1)|~m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_24])]), c_0_34])).
% 0.21/0.39  cnf(c_0_81, negated_conjecture, (m1_connsp_2(esk2_3(esk5_0,u1_struct_0(esk7_0),esk8_0),esk5_0,esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_70]), c_0_25]), c_0_27]), c_0_71]), c_0_72])]), c_0_68])).
% 0.21/0.39  cnf(c_0_82, negated_conjecture, (r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)|r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_78, c_0_22])).
% 0.21/0.39  cnf(c_0_83, negated_conjecture, (~r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)|~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_84, negated_conjecture, (r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk5_0,esk4_0,esk6_0,X2)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_62]), c_0_63]), c_0_25]), c_0_64]), c_0_27]), c_0_65]), c_0_66])]), c_0_67]), c_0_68])).
% 0.21/0.39  cnf(c_0_85, negated_conjecture, (r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_31])]), c_0_82])).
% 0.21/0.39  cnf(c_0_86, negated_conjecture, (~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)|~r1_tmap_1(esk5_0,esk4_0,esk6_0,esk8_0)), inference(rw,[status(thm)],[c_0_83, c_0_22])).
% 0.21/0.39  cnf(c_0_87, negated_conjecture, (r1_tmap_1(X1,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,X1),esk8_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.21/0.39  cnf(c_0_88, negated_conjecture, (~r1_tmap_1(esk7_0,esk4_0,k2_tmap_1(esk5_0,esk4_0,esk6_0,esk7_0),esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_85])])).
% 0.21/0.39  cnf(c_0_89, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_24]), c_0_31])]), c_0_88]), c_0_34]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 90
% 0.21/0.39  # Proof object clause steps            : 61
% 0.21/0.39  # Proof object formula steps           : 29
% 0.21/0.39  # Proof object conjectures             : 45
% 0.21/0.39  # Proof object clause conjectures      : 42
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 31
% 0.21/0.39  # Proof object initial formulas used   : 14
% 0.21/0.39  # Proof object generating inferences   : 20
% 0.21/0.39  # Proof object simplifying inferences  : 80
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 14
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 38
% 0.21/0.39  # Removed in clause preprocessing      : 1
% 0.21/0.39  # Initial clauses in saturation        : 37
% 0.21/0.39  # Processed clauses                    : 156
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 13
% 0.21/0.39  # ...remaining for further processing  : 143
% 0.21/0.39  # Other redundant clauses eliminated   : 5
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 2
% 0.21/0.39  # Backward-rewritten                   : 5
% 0.21/0.39  # Generated clauses                    : 142
% 0.21/0.39  # ...of the previous two non-trivial   : 138
% 0.21/0.39  # Contextual simplify-reflections      : 9
% 0.21/0.39  # Paramodulations                      : 135
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 5
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 93
% 0.21/0.39  #    Positive orientable unit clauses  : 29
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 6
% 0.21/0.39  #    Non-unit-clauses                  : 58
% 0.21/0.39  # Current number of unprocessed clauses: 55
% 0.21/0.39  # ...number of literals in the above   : 400
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 45
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 2240
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 150
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 22
% 0.21/0.39  # Unit Clause-clause subsumption calls : 54
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 4
% 0.21/0.39  # BW rewrite match successes           : 2
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 9424
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.042 s
% 0.21/0.39  # System time              : 0.004 s
% 0.21/0.39  # Total time               : 0.046 s
% 0.21/0.39  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
