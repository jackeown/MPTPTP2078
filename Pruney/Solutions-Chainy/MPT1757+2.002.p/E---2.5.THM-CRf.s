%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:28 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 917 expanded)
%              Number of clauses        :   64 ( 322 expanded)
%              Number of leaves         :   16 ( 219 expanded)
%              Depth                    :   14
%              Number of atoms          :  508 (9821 expanded)
%              Number of equality atoms :   26 ( 546 expanded)
%              Maximal formula depth    :   28 (   6 average)
%              Maximal clause size      :   38 (   4 average)
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

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(dt_k1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(t30_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_hidden(X2,k1_connsp_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X39,X40,X41] :
      ( ( ~ v1_tsep_1(X40,X39)
        | ~ m1_pre_topc(X40,X39)
        | v3_pre_topc(X41,X39)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_pre_topc(X40,X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( v1_tsep_1(X40,X39)
        | ~ v3_pre_topc(X41,X39)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_pre_topc(X40,X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) )
      & ( m1_pre_topc(X40,X39)
        | ~ v3_pre_topc(X41,X39)
        | X41 != u1_struct_0(X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ m1_pre_topc(X40,X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
    & ~ v2_struct_0(esk5_0)
    & v1_tsep_1(esk5_0,esk3_0)
    & m1_pre_topc(esk5_0,esk3_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & esk6_0 = esk7_0
    & ( ~ r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)
      | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0) )
    & ( r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)
      | r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

fof(c_0_19,plain,(
    ! [X24,X25] :
      ( ~ l1_pre_topc(X24)
      | ~ m1_pre_topc(X25,X24)
      | l1_pre_topc(X25) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_20,plain,(
    ! [X22,X23] :
      ( ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | v2_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_21,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | ~ m1_subset_1(X38,u1_struct_0(X36))
      | ~ v3_pre_topc(X37,X36)
      | ~ r2_hidden(X38,X37)
      | m1_connsp_2(X37,X36,X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_22,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( v3_pre_topc(X3,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_pre_topc(X43,X42)
      | m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

fof(c_0_25,plain,(
    ! [X29,X30] :
      ( v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | m1_subset_1(k1_connsp_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_31,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v3_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_tsep_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_37,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])])).

cnf(c_0_42,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_29]),c_0_30]),c_0_32])])).

fof(c_0_43,plain,(
    ! [X34,X35] :
      ( v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,u1_struct_0(X34))
      | r2_hidden(X35,k1_connsp_2(X34,X35)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).

fof(c_0_44,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_connsp_2(X33,X31,X32)
      | m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_45,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1) ),
    inference(csr,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_46,plain,
    ( v3_pre_topc(u1_struct_0(X1),X2)
    | u1_struct_0(X1) != u1_struct_0(X3)
    | ~ v1_tsep_1(X3,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( v1_tsep_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_48,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,X15)
      | v1_xboole_0(X15)
      | r2_hidden(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k1_connsp_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_connsp_2(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,plain,
    ( m1_connsp_2(u1_struct_0(X1),X2,X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ r2_hidden(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_36])).

cnf(c_0_56,negated_conjecture,
    ( v3_pre_topc(u1_struct_0(X1),esk3_0)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_29]),c_0_30]),c_0_32])])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,k1_connsp_2(esk5_0,esk6_0))
    | ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk6_0,k1_connsp_2(esk5_0,esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_39]),c_0_40]),c_0_41]),c_0_42])])).

fof(c_0_60,plain,(
    ! [X50,X51,X52,X53,X54,X55,X56] :
      ( ( ~ r1_tmap_1(X51,X50,X52,X55)
        | r1_tmap_1(X53,X50,k2_tmap_1(X51,X50,X52,X53),X56)
        | ~ r1_tarski(X54,u1_struct_0(X53))
        | ~ m1_connsp_2(X54,X51,X55)
        | X55 != X56
        | ~ m1_subset_1(X56,u1_struct_0(X53))
        | ~ m1_subset_1(X55,u1_struct_0(X51))
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) )
      & ( ~ r1_tmap_1(X53,X50,k2_tmap_1(X51,X50,X52,X53),X56)
        | r1_tmap_1(X51,X50,X52,X55)
        | ~ r1_tarski(X54,u1_struct_0(X53))
        | ~ m1_connsp_2(X54,X51,X55)
        | X55 != X56
        | ~ m1_subset_1(X56,u1_struct_0(X53))
        | ~ m1_subset_1(X55,u1_struct_0(X51))
        | ~ m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X53)
        | ~ m1_pre_topc(X53,X51)
        | ~ v1_funct_1(X52)
        | ~ v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50))))
        | v2_struct_0(X51)
        | ~ v2_pre_topc(X51)
        | ~ l1_pre_topc(X51)
        | v2_struct_0(X50)
        | ~ v2_pre_topc(X50)
        | ~ l1_pre_topc(X50) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).

fof(c_0_61,plain,(
    ! [X26,X27,X28] :
      ( v2_struct_0(X26)
      | ~ l1_pre_topc(X26)
      | v2_struct_0(X27)
      | ~ m1_pre_topc(X27,X26)
      | ~ m1_subset_1(X28,u1_struct_0(X27))
      | m1_subset_1(X28,u1_struct_0(X26)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_connsp_2(X1,esk3_0,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_30]),c_0_32])]),c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( m1_connsp_2(u1_struct_0(X1),esk3_0,X2)
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_30]),c_0_32])]),c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_39])).

cnf(c_0_65,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_66,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | u1_struct_0(X1) != u1_struct_0(esk5_0)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk6_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[c_0_64,c_0_65])).

fof(c_0_70,plain,(
    ! [X44,X45,X46,X47,X48,X49] :
      ( v2_struct_0(X44)
      | ~ v2_pre_topc(X44)
      | ~ l1_pre_topc(X44)
      | v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ v1_funct_1(X46)
      | ~ v1_funct_2(X46,u1_struct_0(X45),u1_struct_0(X44))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X44))))
      | v2_struct_0(X47)
      | ~ m1_pre_topc(X47,X45)
      | ~ m1_subset_1(X48,u1_struct_0(X45))
      | ~ m1_subset_1(X49,u1_struct_0(X47))
      | X48 != X49
      | ~ r1_tmap_1(X45,X44,X46,X48)
      | r1_tmap_1(X47,X44,k2_tmap_1(X45,X44,X46,X47),X49) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

cnf(c_0_71,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_66,c_0_52])]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_76,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)
    | r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_29])])).

fof(c_0_80,plain,(
    ! [X12,X13] :
      ( ( r1_tarski(X12,X13)
        | X12 != X13 )
      & ( r1_tarski(X13,X12)
        | X12 != X13 )
      & ( ~ r1_tarski(X12,X13)
        | ~ r1_tarski(X13,X12)
        | X12 = X13 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_81,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,esk4_0,X1)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X2,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,X2),X1)
    | ~ m1_connsp_2(X3,esk3_0,X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_tarski(X3,u1_struct_0(X2)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_74]),c_0_30]),c_0_75]),c_0_32]),c_0_76])]),c_0_54]),c_0_77])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk6_0)
    | r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_27])).

cnf(c_0_84,negated_conjecture,
    ( m1_connsp_2(u1_struct_0(esk5_0),esk3_0,X1)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk3_0)
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_79]),c_0_30]),c_0_32])]),c_0_54])).

cnf(c_0_85,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_86,plain,
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
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_81]),c_0_67])).

cnf(c_0_87,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)
    | ~ m1_connsp_2(X1,esk3_0,esk6_0)
    | ~ r1_tarski(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_29]),c_0_39])]),c_0_40])).

cnf(c_0_88,negated_conjecture,
    ( m1_connsp_2(u1_struct_0(esk5_0),esk3_0,X1)
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_56]),c_0_29])])).

cnf(c_0_89,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)
    | ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_91,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),X2)
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk3_0,esk2_0,esk4_0,X2)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_72]),c_0_73]),c_0_74]),c_0_30]),c_0_75]),c_0_32]),c_0_76])]),c_0_54]),c_0_77])).

cnf(c_0_92,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89]),c_0_69])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk6_0)
    | ~ r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_90,c_0_27])).

cnf(c_0_94,negated_conjecture,
    ( r1_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),esk6_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(esk6_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_92])])).

cnf(c_0_96,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_39]),c_0_29])]),c_0_95]),c_0_40]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:09:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.39  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t67_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 0.20/0.39  fof(t16_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_tsep_1(X2,X1)&m1_pre_topc(X2,X1))<=>v3_pre_topc(X3,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 0.20/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.39  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.20/0.39  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.20/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.39  fof(dt_k1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 0.20/0.39  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.20/0.39  fof(t30_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_hidden(X2,k1_connsp_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 0.20/0.39  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.20/0.39  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.39  fof(t65_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>![X7]:(m1_subset_1(X7,u1_struct_0(X4))=>(((r1_tarski(X5,u1_struct_0(X4))&m1_connsp_2(X5,X2,X6))&X6=X7)=>(r1_tmap_1(X2,X1,X3,X6)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X7)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 0.20/0.39  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.39  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.20/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:(((~(v2_struct_0(X4))&v1_tsep_1(X4,X2))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>(X5=X6=>(r1_tmap_1(X2,X1,X3,X5)<=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))))), inference(assume_negation,[status(cth)],[t67_tmap_1])).
% 0.20/0.39  fof(c_0_17, plain, ![X39, X40, X41]:((~v1_tsep_1(X40,X39)|~m1_pre_topc(X40,X39)|v3_pre_topc(X41,X39)|X41!=u1_struct_0(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~m1_pre_topc(X40,X39)|(~v2_pre_topc(X39)|~l1_pre_topc(X39)))&((v1_tsep_1(X40,X39)|~v3_pre_topc(X41,X39)|X41!=u1_struct_0(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~m1_pre_topc(X40,X39)|(~v2_pre_topc(X39)|~l1_pre_topc(X39)))&(m1_pre_topc(X40,X39)|~v3_pre_topc(X41,X39)|X41!=u1_struct_0(X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39)))|~m1_pre_topc(X40,X39)|(~v2_pre_topc(X39)|~l1_pre_topc(X39))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t16_tsep_1])])])])).
% 0.20/0.39  fof(c_0_18, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&(((~v2_struct_0(esk5_0)&v1_tsep_1(esk5_0,esk3_0))&m1_pre_topc(esk5_0,esk3_0))&(m1_subset_1(esk6_0,u1_struct_0(esk3_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&(esk6_0=esk7_0&((~r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0))&(r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)|r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.20/0.39  fof(c_0_19, plain, ![X24, X25]:(~l1_pre_topc(X24)|(~m1_pre_topc(X25,X24)|l1_pre_topc(X25))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.39  fof(c_0_20, plain, ![X22, X23]:(~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|v2_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.20/0.39  fof(c_0_21, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~m1_subset_1(X38,u1_struct_0(X36))|(~v3_pre_topc(X37,X36)|~r2_hidden(X38,X37)|m1_connsp_2(X37,X36,X38))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.20/0.39  fof(c_0_22, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.39  cnf(c_0_23, plain, (v3_pre_topc(X3,X2)|~v1_tsep_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  fof(c_0_24, plain, ![X42, X43]:(~l1_pre_topc(X42)|(~m1_pre_topc(X43,X42)|m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.39  fof(c_0_25, plain, ![X29, X30]:(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|~m1_subset_1(X30,u1_struct_0(X29))|m1_subset_1(k1_connsp_2(X29,X30),k1_zfmisc_1(u1_struct_0(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_connsp_2])])])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_28, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (m1_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_31, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_33, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_34, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.39  cnf(c_0_35, plain, (v3_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_tsep_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_36, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.39  fof(c_0_37, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.20/0.39  cnf(c_0_38, plain, (v2_struct_0(X1)|m1_subset_1(k1_connsp_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30])])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (v2_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_29]), c_0_30]), c_0_32])])).
% 0.20/0.39  fof(c_0_43, plain, ![X34, X35]:(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(~m1_subset_1(X35,u1_struct_0(X34))|r2_hidden(X35,k1_connsp_2(X34,X35)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t30_connsp_2])])])])).
% 0.20/0.39  fof(c_0_44, plain, ![X31, X32, X33]:(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|~m1_subset_1(X32,u1_struct_0(X31))|(~m1_connsp_2(X33,X31,X32)|m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.20/0.39  cnf(c_0_45, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|~v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)), inference(csr,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.39  cnf(c_0_46, plain, (v3_pre_topc(u1_struct_0(X1),X2)|u1_struct_0(X1)!=u1_struct_0(X3)|~v1_tsep_1(X3,X2)|~m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (v1_tsep_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  fof(c_0_48, plain, ![X14, X15]:(~m1_subset_1(X14,X15)|(v1_xboole_0(X15)|r2_hidden(X14,X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.39  cnf(c_0_49, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(k1_connsp_2(esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.20/0.39  cnf(c_0_51, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_connsp_2(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_52, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_55, plain, (m1_connsp_2(u1_struct_0(X1),X2,X3)|v2_struct_0(X2)|~v3_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~r2_hidden(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_45, c_0_36])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (v3_pre_topc(u1_struct_0(X1),esk3_0)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_29]), c_0_30]), c_0_32])])).
% 0.20/0.39  cnf(c_0_57, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,k1_connsp_2(esk5_0,esk6_0))|~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (r2_hidden(esk6_0,k1_connsp_2(esk5_0,esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_39]), c_0_40]), c_0_41]), c_0_42])])).
% 0.20/0.39  fof(c_0_60, plain, ![X50, X51, X52, X53, X54, X55, X56]:((~r1_tmap_1(X51,X50,X52,X55)|r1_tmap_1(X53,X50,k2_tmap_1(X51,X50,X52,X53),X56)|(~r1_tarski(X54,u1_struct_0(X53))|~m1_connsp_2(X54,X51,X55)|X55!=X56)|~m1_subset_1(X56,u1_struct_0(X53))|~m1_subset_1(X55,u1_struct_0(X51))|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X51)))|(v2_struct_0(X53)|~m1_pre_topc(X53,X51))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50)))))|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)))&(~r1_tmap_1(X53,X50,k2_tmap_1(X51,X50,X52,X53),X56)|r1_tmap_1(X51,X50,X52,X55)|(~r1_tarski(X54,u1_struct_0(X53))|~m1_connsp_2(X54,X51,X55)|X55!=X56)|~m1_subset_1(X56,u1_struct_0(X53))|~m1_subset_1(X55,u1_struct_0(X51))|~m1_subset_1(X54,k1_zfmisc_1(u1_struct_0(X51)))|(v2_struct_0(X53)|~m1_pre_topc(X53,X51))|(~v1_funct_1(X52)|~v1_funct_2(X52,u1_struct_0(X51),u1_struct_0(X50))|~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X50)))))|(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51))|(v2_struct_0(X50)|~v2_pre_topc(X50)|~l1_pre_topc(X50)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_tmap_1])])])])])).
% 0.20/0.39  fof(c_0_61, plain, ![X26, X27, X28]:(v2_struct_0(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~m1_pre_topc(X27,X26)|(~m1_subset_1(X28,u1_struct_0(X27))|m1_subset_1(X28,u1_struct_0(X26))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.39  cnf(c_0_62, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_connsp_2(X1,esk3_0,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_30]), c_0_32])]), c_0_54])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (m1_connsp_2(u1_struct_0(X1),esk3_0,X2)|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_30]), c_0_32])]), c_0_54])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_57, c_0_39])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.20/0.39  cnf(c_0_66, plain, (r1_tmap_1(X3,X2,X4,X6)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|~r1_tarski(X7,u1_struct_0(X1))|~m1_connsp_2(X7,X3,X6)|X6!=X5|~m1_subset_1(X5,u1_struct_0(X1))|~m1_subset_1(X6,u1_struct_0(X3))|~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X1,X3)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.20/0.39  cnf(c_0_67, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(esk3_0)))|u1_struct_0(X1)!=u1_struct_0(esk5_0)|~m1_pre_topc(X1,esk3_0)|~r2_hidden(esk6_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.39  fof(c_0_70, plain, ![X44, X45, X46, X47, X48, X49]:(v2_struct_0(X44)|~v2_pre_topc(X44)|~l1_pre_topc(X44)|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~v1_funct_1(X46)|~v1_funct_2(X46,u1_struct_0(X45),u1_struct_0(X44))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X45),u1_struct_0(X44))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X45)|(~m1_subset_1(X48,u1_struct_0(X45))|(~m1_subset_1(X49,u1_struct_0(X47))|(X48!=X49|~r1_tmap_1(X45,X44,X46,X48)|r1_tmap_1(X47,X44,k2_tmap_1(X45,X44,X46,X47),X49)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_71, plain, (r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X5)|~r1_tmap_1(X5,X2,k2_tmap_1(X1,X2,X3,X5),X4)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~v1_funct_1(X3)|~m1_connsp_2(X6,X1,X4)|~m1_pre_topc(X5,X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~v2_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_subset_1(X4,u1_struct_0(X5))|~r1_tarski(X6,u1_struct_0(X5))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_66, c_0_52])]), c_0_67])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_76, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)|r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_79, negated_conjecture, (m1_subset_1(u1_struct_0(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_29])])).
% 0.20/0.39  fof(c_0_80, plain, ![X12, X13]:(((r1_tarski(X12,X13)|X12!=X13)&(r1_tarski(X13,X12)|X12!=X13))&(~r1_tarski(X12,X13)|~r1_tarski(X13,X12)|X12=X13)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.39  cnf(c_0_81, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.39  cnf(c_0_82, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,esk4_0,X1)|v2_struct_0(X2)|~r1_tmap_1(X2,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,X2),X1)|~m1_connsp_2(X3,esk3_0,X1)|~m1_pre_topc(X2,esk3_0)|~m1_subset_1(X1,u1_struct_0(X2))|~r1_tarski(X3,u1_struct_0(X2))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_74]), c_0_30]), c_0_75]), c_0_32]), c_0_76])]), c_0_54]), c_0_77])).
% 0.20/0.39  cnf(c_0_83, negated_conjecture, (r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk6_0)|r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)), inference(rw,[status(thm)],[c_0_78, c_0_27])).
% 0.20/0.39  cnf(c_0_84, negated_conjecture, (m1_connsp_2(u1_struct_0(esk5_0),esk3_0,X1)|~v3_pre_topc(u1_struct_0(esk5_0),esk3_0)|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_79]), c_0_30]), c_0_32])]), c_0_54])).
% 0.20/0.39  cnf(c_0_85, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.39  cnf(c_0_86, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_81]), c_0_67])).
% 0.20/0.39  cnf(c_0_87, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)|~m1_connsp_2(X1,esk3_0,esk6_0)|~r1_tarski(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_29]), c_0_39])]), c_0_40])).
% 0.20/0.39  cnf(c_0_88, negated_conjecture, (m1_connsp_2(u1_struct_0(esk5_0),esk3_0,X1)|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_56]), c_0_29])])).
% 0.20/0.39  cnf(c_0_89, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_85])).
% 0.20/0.39  cnf(c_0_90, negated_conjecture, (~r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)|~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.39  cnf(c_0_91, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),X2)|v2_struct_0(X1)|~r1_tmap_1(esk3_0,esk2_0,esk4_0,X2)|~m1_pre_topc(X1,esk3_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_72]), c_0_73]), c_0_74]), c_0_30]), c_0_75]), c_0_32]), c_0_76])]), c_0_54]), c_0_77])).
% 0.20/0.39  cnf(c_0_92, negated_conjecture, (r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89]), c_0_69])])).
% 0.20/0.39  cnf(c_0_93, negated_conjecture, (~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk6_0)|~r1_tmap_1(esk3_0,esk2_0,esk4_0,esk6_0)), inference(rw,[status(thm)],[c_0_90, c_0_27])).
% 0.20/0.39  cnf(c_0_94, negated_conjecture, (r1_tmap_1(X1,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,X1),esk6_0)|v2_struct_0(X1)|~m1_pre_topc(X1,esk3_0)|~m1_subset_1(esk6_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.20/0.39  cnf(c_0_95, negated_conjecture, (~r1_tmap_1(esk5_0,esk2_0,k2_tmap_1(esk3_0,esk2_0,esk4_0,esk5_0),esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_92])])).
% 0.20/0.39  cnf(c_0_96, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_39]), c_0_29])]), c_0_95]), c_0_40]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 97
% 0.20/0.39  # Proof object clause steps            : 64
% 0.20/0.39  # Proof object formula steps           : 33
% 0.20/0.39  # Proof object conjectures             : 45
% 0.20/0.39  # Proof object clause conjectures      : 42
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 32
% 0.20/0.39  # Proof object initial formulas used   : 16
% 0.20/0.39  # Proof object generating inferences   : 22
% 0.20/0.39  # Proof object simplifying inferences  : 76
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 17
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 39
% 0.20/0.39  # Removed in clause preprocessing      : 1
% 0.20/0.39  # Initial clauses in saturation        : 38
% 0.20/0.39  # Processed clauses                    : 170
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 25
% 0.20/0.39  # ...remaining for further processing  : 144
% 0.20/0.39  # Other redundant clauses eliminated   : 5
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 11
% 0.20/0.39  # Backward-rewritten                   : 3
% 0.20/0.39  # Generated clauses                    : 205
% 0.20/0.39  # ...of the previous two non-trivial   : 180
% 0.20/0.39  # Contextual simplify-reflections      : 7
% 0.20/0.39  # Paramodulations                      : 196
% 0.20/0.39  # Factorizations                       : 2
% 0.20/0.39  # Equation resolutions                 : 5
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 123
% 0.20/0.39  #    Positive orientable unit clauses  : 38
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 11
% 0.20/0.39  #    Non-unit-clauses                  : 74
% 0.20/0.39  # Current number of unprocessed clauses: 48
% 0.20/0.39  # ...number of literals in the above   : 181
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 16
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 1485
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 237
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 30
% 0.20/0.39  # Unit Clause-clause subsumption calls : 85
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 10
% 0.20/0.39  # BW rewrite match successes           : 3
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 8552
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.038 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.045 s
% 0.20/0.39  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
