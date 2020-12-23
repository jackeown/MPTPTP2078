%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:10 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 (12981 expanded)
%              Number of clauses        :   87 (4145 expanded)
%              Number of leaves         :   18 (3224 expanded)
%              Depth                    :   20
%              Number of atoms          :  705 (107427 expanded)
%              Number of equality atoms :   48 (7709 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   48 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_tmap_1)).

fof(dt_k4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_pre_topc(X2,X1) )
     => ( v1_funct_1(k4_tmap_1(X1,X2))
        & v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
        & m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_tmap_1)).

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

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

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

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(dt_k3_tmap_1,axiom,(
    ! [X1,X2,X3,X4,X5] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_pre_topc(X3,X1)
        & m1_pre_topc(X4,X1)
        & v1_funct_1(X5)
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
     => ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
        & v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t59_tmap_1,axiom,(
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
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(t74_tmap_1,axiom,(
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
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t95_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,u1_struct_0(X2))
               => k1_funct_1(k4_tmap_1(X1,X2),X3) = X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_tmap_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

fof(c_0_19,plain,(
    ! [X40,X41] :
      ( ( v1_funct_1(k4_tmap_1(X40,X41))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) )
      & ( v1_funct_2(k4_tmap_1(X40,X41),u1_struct_0(X41),u1_struct_0(X40))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) )
      & ( m1_subset_1(k4_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))
        | v2_struct_0(X40)
        | ~ v2_pre_topc(X40)
        | ~ l1_pre_topc(X40)
        | ~ m1_pre_topc(X41,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).

fof(c_0_20,negated_conjecture,(
    ! [X64] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & m1_pre_topc(esk3_0,esk2_0)
      & v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X64,u1_struct_0(esk2_0))
        | ~ r2_hidden(X64,u1_struct_0(esk3_0))
        | X64 = k1_funct_1(esk4_0,X64) )
      & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).

fof(c_0_21,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | l1_pre_topc(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X20,X21] :
      ( ~ v2_pre_topc(X20)
      | ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | v2_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_23,plain,(
    ! [X30,X31,X32,X33,X34] :
      ( v2_struct_0(X30)
      | ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X31)
      | ~ v2_pre_topc(X31)
      | ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X30)
      | ~ m1_pre_topc(X33,X30)
      | ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))
      | ~ m1_pre_topc(X33,X32)
      | k3_tmap_1(X30,X31,X32,X33,X34) = k2_partfun1(u1_struct_0(X32),u1_struct_0(X31),X34,u1_struct_0(X33)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_24,plain,(
    ! [X55,X56,X57] :
      ( ~ v2_pre_topc(X55)
      | ~ l1_pre_topc(X55)
      | ~ m1_pre_topc(X56,X55)
      | ~ m1_pre_topc(X57,X56)
      | m1_pre_topc(X57,X55) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).

fof(c_0_25,plain,(
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

cnf(c_0_26,plain,
    ( m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( v1_funct_1(k4_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( m1_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_37,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28])])).

cnf(c_0_40,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_27]),c_0_28]),c_0_29])])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( v1_funct_1(k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_44,plain,(
    ! [X44] :
      ( ~ l1_pre_topc(X44)
      | m1_pre_topc(X44,X44) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_45,plain,
    ( k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_pre_topc(X4,X3)
    | ~ m1_pre_topc(X3,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X1)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1)
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_28]),c_0_39]),c_0_29]),c_0_40]),c_0_41]),c_0_42])]),c_0_30]),c_0_43])).

cnf(c_0_47,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_48,plain,(
    ! [X35,X36,X37,X38,X39] :
      ( ( v1_funct_1(k3_tmap_1(X35,X36,X37,X38,X39))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_pre_topc(X37,X35)
        | ~ m1_pre_topc(X38,X35)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36)))) )
      & ( v1_funct_2(k3_tmap_1(X35,X36,X37,X38,X39),u1_struct_0(X38),u1_struct_0(X36))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_pre_topc(X37,X35)
        | ~ m1_pre_topc(X38,X35)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36)))) )
      & ( m1_subset_1(k3_tmap_1(X35,X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36))))
        | v2_struct_0(X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35)
        | v2_struct_0(X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36)
        | ~ m1_pre_topc(X37,X35)
        | ~ m1_pre_topc(X38,X35)
        | ~ v1_funct_1(X39)
        | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X36))
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36)))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).

cnf(c_0_49,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)) = k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,esk3_0)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_38]),c_0_28]),c_0_29]),c_0_41]),c_0_42])]),c_0_30])).

cnf(c_0_50,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_39])])).

cnf(c_0_51,plain,
    ( m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) = k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_47]),c_0_50]),c_0_39])])).

cnf(c_0_53,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_38]),c_0_28]),c_0_29]),c_0_41]),c_0_42])]),c_0_30])).

cnf(c_0_54,plain,
    ( v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0) = k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_39]),c_0_40])]),c_0_43])).

cnf(c_0_56,plain,
    ( v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_57,plain,(
    ! [X16,X17,X18,X19] :
      ( ( ~ r2_funct_2(X16,X17,X18,X19)
        | X18 = X19
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X18 != X19
        | r2_funct_2(X16,X17,X18,X19)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X16,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X16,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_59,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_28]),c_0_29]),c_0_41]),c_0_42])]),c_0_30])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) = k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(rw,[status(thm)],[c_0_52,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v2_struct_0(X1)
    | v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_38]),c_0_28]),c_0_29]),c_0_41]),c_0_42])]),c_0_30])).

fof(c_0_62,plain,(
    ! [X45,X46,X47,X48,X49] :
      ( ( m1_subset_1(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X46))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( r2_hidden(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X47))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) )
      & ( k3_funct_2(u1_struct_0(X46),u1_struct_0(X45),X48,esk1_5(X45,X46,X47,X48,X49)) != k1_funct_1(X49,esk1_5(X45,X46,X47,X48,X49))
        | r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45))))
        | ~ v1_funct_1(X48)
        | ~ v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45))))
        | v2_struct_0(X47)
        | ~ m1_pre_topc(X47,X46)
        | v2_struct_0(X46)
        | ~ v2_pre_topc(X46)
        | ~ l1_pre_topc(X46)
        | v2_struct_0(X45)
        | ~ v2_pre_topc(X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

cnf(c_0_63,plain,
    ( X3 = X4
    | ~ r2_funct_2(X1,X2,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk3_0,esk2_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_39]),c_0_40])]),c_0_43])).

cnf(c_0_66,negated_conjecture,
    ( k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) = k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk3_0,esk2_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_39]),c_0_40])]),c_0_43])).

fof(c_0_68,plain,(
    ! [X51,X52,X53,X54] :
      ( v2_struct_0(X51)
      | ~ v2_pre_topc(X51)
      | ~ l1_pre_topc(X51)
      | v2_struct_0(X52)
      | ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | v2_struct_0(X53)
      | ~ m1_pre_topc(X53,X51)
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,u1_struct_0(X53),u1_struct_0(X52))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X52))))
      | r2_funct_2(u1_struct_0(X53),u1_struct_0(X52),X54,k3_tmap_1(X51,X52,X53,X53,X54)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

fof(c_0_69,plain,(
    ! [X42,X43] :
      ( ~ l1_pre_topc(X42)
      | ~ m1_pre_topc(X43,X42)
      | m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_70,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_71,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_75,negated_conjecture,
    ( X1 = k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_2(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( v1_funct_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,negated_conjecture,
    ( v1_funct_2(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_66])).

cnf(c_0_78,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

fof(c_0_79,plain,(
    ! [X9,X10,X11] :
      ( ~ r2_hidden(X9,X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | m1_subset_1(X9,X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_80,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)
    | r2_hidden(esk1_5(esk2_0,X1,esk3_0,X2,esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_28]),c_0_29]),c_0_72]),c_0_73])]),c_0_43]),c_0_30])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)
    | m1_subset_1(esk1_5(esk2_0,X1,esk3_0,X2,esk4_0),u1_struct_0(X1))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_71]),c_0_28]),c_0_29]),c_0_72]),c_0_73])]),c_0_43]),c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( X1 = k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ m1_pre_topc(esk3_0,esk3_0)
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_38]),c_0_28]),c_0_29]),c_0_41]),c_0_42])]),c_0_43]),c_0_30])).

cnf(c_0_85,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk1_5(X2,X1,X4,X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_86,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_27]),c_0_28])])).

cnf(c_0_88,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_38]),c_0_55]),c_0_66]),c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

fof(c_0_89,plain,(
    ! [X12,X13,X14,X15] :
      ( v1_xboole_0(X12)
      | ~ v1_funct_1(X14)
      | ~ v1_funct_2(X14,X12,X13)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | ~ m1_subset_1(X15,X12)
      | k3_funct_2(X12,X13,X14,X15) = k1_funct_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_90,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_38]),c_0_55]),c_0_66]),c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_91,negated_conjecture,
    ( X1 = k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))
    | ~ v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_47]),c_0_39])])).

cnf(c_0_92,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_27]),c_0_28]),c_0_29])]),c_0_30])).

cnf(c_0_93,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0)) != k1_funct_1(esk4_0,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_71]),c_0_28]),c_0_29]),c_0_72]),c_0_73])]),c_0_43]),c_0_30])).

cnf(c_0_94,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)
    | r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_47]),c_0_39])])).

cnf(c_0_96,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_47]),c_0_39])])).

cnf(c_0_98,negated_conjecture,
    ( k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)) = k4_tmap_1(esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_41]),c_0_42]),c_0_38])])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_100,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)
    | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) != k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_38]),c_0_55]),c_0_66]),c_0_39]),c_0_40]),c_0_41]),c_0_42])]),c_0_43])).

cnf(c_0_101,negated_conjecture,
    ( X1 = k1_funct_1(esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_102,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)
    | m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

fof(c_0_103,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_104,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)
    | v1_xboole_0(u1_struct_0(esk3_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_38]),c_0_42])]),c_0_41])])).

cnf(c_0_105,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98]),c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) != k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ m1_pre_topc(esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_98]),c_0_99])).

cnf(c_0_107,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_95]),c_0_102])).

cnf(c_0_108,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

fof(c_0_110,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_111,plain,(
    ! [X58,X59,X60] :
      ( v2_struct_0(X58)
      | ~ v2_pre_topc(X58)
      | ~ l1_pre_topc(X58)
      | v2_struct_0(X59)
      | ~ m1_pre_topc(X59,X58)
      | ~ m1_subset_1(X60,u1_struct_0(X58))
      | ~ r2_hidden(X60,u1_struct_0(X59))
      | k1_funct_1(k4_tmap_1(X58,X59),X60) = X60 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).

cnf(c_0_112,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) != k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_47]),c_0_39])])).

cnf(c_0_113,negated_conjecture,
    ( k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_107,c_0_98]),c_0_99])).

cnf(c_0_114,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_43])).

cnf(c_0_115,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_116,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_funct_1(k4_tmap_1(X1,X2),X3) = X3
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_111])).

cnf(c_0_117,negated_conjecture,
    ( r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_98]),c_0_99])).

cnf(c_0_118,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) != esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_112,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_39])])).

cnf(c_0_120,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(X1,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) = esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_43])).

cnf(c_0_121,negated_conjecture,
    ( m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102,c_0_98]),c_0_99])).

cnf(c_0_122,negated_conjecture,
    ( k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)) != esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_123,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_27]),c_0_28]),c_0_29])]),c_0_122]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:26:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.51  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S059I
% 0.21/0.51  # and selection function SelectComplexExceptUniqMaxPosHorn.
% 0.21/0.51  #
% 0.21/0.51  # Preprocessing time       : 0.046 s
% 0.21/0.51  # Presaturation interreduction done
% 0.21/0.51  
% 0.21/0.51  # Proof found!
% 0.21/0.51  # SZS status Theorem
% 0.21/0.51  # SZS output start CNFRefutation
% 0.21/0.51  fof(t96_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_tmap_1)).
% 0.21/0.51  fof(dt_k4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_pre_topc(X2,X1))=>((v1_funct_1(k4_tmap_1(X1,X2))&v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_tmap_1)).
% 0.21/0.51  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.51  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.21/0.51  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.21/0.51  fof(t7_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X2)=>m1_pre_topc(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tsep_1)).
% 0.21/0.51  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.21/0.51  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.21/0.51  fof(dt_k3_tmap_1, axiom, ![X1, X2, X3, X4, X5]:(((((((((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_pre_topc(X3,X1))&m1_pre_topc(X4,X1))&v1_funct_1(X5))&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))&v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 0.21/0.51  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.21/0.51  fof(t59_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))))=>(![X6]:(m1_subset_1(X6,u1_struct_0(X2))=>(r2_hidden(X6,u1_struct_0(X3))=>k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6)=k1_funct_1(X5,X6)))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_tmap_1)).
% 0.21/0.51  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.21/0.51  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.21/0.51  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.51  fof(redefinition_k3_funct_2, axiom, ![X1, X2, X3, X4]:(((((~(v1_xboole_0(X1))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&m1_subset_1(X4,X1))=>k3_funct_2(X1,X2,X3,X4)=k1_funct_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 0.21/0.51  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.21/0.51  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.51  fof(t95_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_hidden(X3,u1_struct_0(X2))=>k1_funct_1(k4_tmap_1(X1,X2),X3)=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_tmap_1)).
% 0.21/0.51  fof(c_0_18, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,u1_struct_0(X2))=>X4=k1_funct_1(X3,X4)))=>r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3)))))), inference(assume_negation,[status(cth)],[t96_tmap_1])).
% 0.21/0.51  fof(c_0_19, plain, ![X40, X41]:(((v1_funct_1(k4_tmap_1(X40,X41))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40)))&(v1_funct_2(k4_tmap_1(X40,X41),u1_struct_0(X41),u1_struct_0(X40))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40))))&(m1_subset_1(k4_tmap_1(X40,X41),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(X40))))|(v2_struct_0(X40)|~v2_pre_topc(X40)|~l1_pre_topc(X40)|~m1_pre_topc(X41,X40)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_tmap_1])])])])).
% 0.21/0.51  fof(c_0_20, negated_conjecture, ![X64]:(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))))&((~m1_subset_1(X64,u1_struct_0(esk2_0))|(~r2_hidden(X64,u1_struct_0(esk3_0))|X64=k1_funct_1(esk4_0,X64)))&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])])).
% 0.21/0.51  fof(c_0_21, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|l1_pre_topc(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.51  fof(c_0_22, plain, ![X20, X21]:(~v2_pre_topc(X20)|~l1_pre_topc(X20)|(~m1_pre_topc(X21,X20)|v2_pre_topc(X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.21/0.51  fof(c_0_23, plain, ![X30, X31, X32, X33, X34]:(v2_struct_0(X30)|~v2_pre_topc(X30)|~l1_pre_topc(X30)|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)|(~m1_pre_topc(X32,X30)|(~m1_pre_topc(X33,X30)|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X32),u1_struct_0(X31))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X32),u1_struct_0(X31))))|(~m1_pre_topc(X33,X32)|k3_tmap_1(X30,X31,X32,X33,X34)=k2_partfun1(u1_struct_0(X32),u1_struct_0(X31),X34,u1_struct_0(X33)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.21/0.51  fof(c_0_24, plain, ![X55, X56, X57]:(~v2_pre_topc(X55)|~l1_pre_topc(X55)|(~m1_pre_topc(X56,X55)|(~m1_pre_topc(X57,X56)|m1_pre_topc(X57,X55)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_tsep_1])])])).
% 0.21/0.51  fof(c_0_25, plain, ![X26, X27, X28, X29]:(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,u1_struct_0(X26),u1_struct_0(X27))|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X27))))|(~m1_pre_topc(X29,X26)|k2_tmap_1(X26,X27,X28,X29)=k2_partfun1(u1_struct_0(X26),u1_struct_0(X27),X28,u1_struct_0(X29)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.21/0.51  cnf(c_0_26, plain, (m1_subset_1(k4_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_31, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.51  cnf(c_0_32, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.51  cnf(c_0_33, plain, (v1_funct_2(k4_tmap_1(X1,X2),u1_struct_0(X2),u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_34, plain, (v1_funct_1(k4_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.51  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.21/0.51  cnf(c_0_36, plain, (m1_pre_topc(X3,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.21/0.51  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.51  cnf(c_0_38, negated_conjecture, (m1_subset_1(k4_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.21/0.51  cnf(c_0_39, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_27]), c_0_28])])).
% 0.21/0.51  cnf(c_0_40, negated_conjecture, (v2_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_27]), c_0_28]), c_0_29])])).
% 0.21/0.51  cnf(c_0_41, negated_conjecture, (v1_funct_2(k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.21/0.51  cnf(c_0_42, negated_conjecture, (v1_funct_1(k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.21/0.51  cnf(c_0_43, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  fof(c_0_44, plain, ![X44]:(~l1_pre_topc(X44)|m1_pre_topc(X44,X44)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.21/0.51  cnf(c_0_45, plain, (k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X2)|~m1_pre_topc(X4,X3)|~m1_pre_topc(X3,X1)|~l1_pre_topc(X2)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~v2_pre_topc(X1)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X5)|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(csr,[status(thm)],[c_0_35, c_0_36])).
% 0.21/0.51  cnf(c_0_46, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X1))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),X1)|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_28]), c_0_39]), c_0_29]), c_0_40]), c_0_41]), c_0_42])]), c_0_30]), c_0_43])).
% 0.21/0.51  cnf(c_0_47, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.21/0.51  fof(c_0_48, plain, ![X35, X36, X37, X38, X39]:(((v1_funct_1(k3_tmap_1(X35,X36,X37,X38,X39))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_pre_topc(X37,X35)|~m1_pre_topc(X38,X35)|~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36))))))&(v1_funct_2(k3_tmap_1(X35,X36,X37,X38,X39),u1_struct_0(X38),u1_struct_0(X36))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_pre_topc(X37,X35)|~m1_pre_topc(X38,X35)|~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36)))))))&(m1_subset_1(k3_tmap_1(X35,X36,X37,X38,X39),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X36))))|(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|~m1_pre_topc(X37,X35)|~m1_pre_topc(X38,X35)|~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X36))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X36))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_tmap_1])])])])).
% 0.21/0.51  cnf(c_0_49, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0))=k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(X2))|v2_struct_0(X1)|~m1_pre_topc(X2,esk3_0)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_38]), c_0_28]), c_0_29]), c_0_41]), c_0_42])]), c_0_30])).
% 0.21/0.51  cnf(c_0_50, negated_conjecture, (k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),u1_struct_0(esk3_0))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_39])])).
% 0.21/0.51  cnf(c_0_51, plain, (m1_subset_1(k3_tmap_1(X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.51  cnf(c_0_52, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))=k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_47]), c_0_50]), c_0_39])])).
% 0.21/0.51  cnf(c_0_53, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_38]), c_0_28]), c_0_29]), c_0_41]), c_0_42])]), c_0_30])).
% 0.21/0.51  cnf(c_0_54, plain, (v1_funct_1(k3_tmap_1(X1,X2,X3,X4,X5))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.51  cnf(c_0_55, negated_conjecture, (k2_tmap_1(esk3_0,esk2_0,k4_tmap_1(esk2_0,esk3_0),esk3_0)=k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_39]), c_0_40])]), c_0_43])).
% 0.21/0.51  cnf(c_0_56, plain, (v1_funct_2(k3_tmap_1(X1,X2,X3,X4,X5),u1_struct_0(X4),u1_struct_0(X2))|v2_struct_0(X1)|v2_struct_0(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.51  fof(c_0_57, plain, ![X16, X17, X18, X19]:((~r2_funct_2(X16,X17,X18,X19)|X18=X19|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|~v1_funct_1(X19)|~v1_funct_2(X19,X16,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))&(X18!=X19|r2_funct_2(X16,X17,X18,X19)|(~v1_funct_1(X18)|~v1_funct_2(X18,X16,X17)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|~v1_funct_1(X19)|~v1_funct_2(X19,X16,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.21/0.51  cnf(c_0_58, negated_conjecture, (m1_subset_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.21/0.51  cnf(c_0_59, negated_conjecture, (v2_struct_0(X1)|v1_funct_1(k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)))|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_38]), c_0_28]), c_0_29]), c_0_41]), c_0_42])]), c_0_30])).
% 0.21/0.51  cnf(c_0_60, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))=k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(rw,[status(thm)],[c_0_52, c_0_55])).
% 0.21/0.51  cnf(c_0_61, negated_conjecture, (v2_struct_0(X1)|v1_funct_2(k3_tmap_1(X1,esk2_0,esk3_0,X2,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_pre_topc(esk3_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_38]), c_0_28]), c_0_29]), c_0_41]), c_0_42])]), c_0_30])).
% 0.21/0.51  fof(c_0_62, plain, ![X45, X46, X47, X48, X49]:((m1_subset_1(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X46))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&((r2_hidden(esk1_5(X45,X46,X47,X48,X49),u1_struct_0(X47))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)))&(k3_funct_2(u1_struct_0(X46),u1_struct_0(X45),X48,esk1_5(X45,X46,X47,X48,X49))!=k1_funct_1(X49,esk1_5(X45,X46,X47,X48,X49))|r2_funct_2(u1_struct_0(X47),u1_struct_0(X45),k2_tmap_1(X46,X45,X48,X47),X49)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X45))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X45)))))|(~v1_funct_1(X48)|~v1_funct_2(X48,u1_struct_0(X46),u1_struct_0(X45))|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X45)))))|(v2_struct_0(X47)|~m1_pre_topc(X47,X46))|(v2_struct_0(X46)|~v2_pre_topc(X46)|~l1_pre_topc(X46))|(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).
% 0.21/0.51  cnf(c_0_63, plain, (X3=X4|~r2_funct_2(X1,X2,X3,X4)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X4)|~v1_funct_2(X4,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.21/0.51  cnf(c_0_64, negated_conjecture, (m1_subset_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_58, c_0_27])).
% 0.21/0.51  cnf(c_0_65, negated_conjecture, (v1_funct_1(k3_tmap_1(esk3_0,esk2_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_47]), c_0_39]), c_0_40])]), c_0_43])).
% 0.21/0.51  cnf(c_0_66, negated_conjecture, (k3_tmap_1(esk3_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))=k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.21/0.51  cnf(c_0_67, negated_conjecture, (v1_funct_2(k3_tmap_1(esk3_0,esk2_0,esk3_0,X1,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_39]), c_0_40])]), c_0_43])).
% 0.21/0.51  fof(c_0_68, plain, ![X51, X52, X53, X54]:(v2_struct_0(X51)|~v2_pre_topc(X51)|~l1_pre_topc(X51)|(v2_struct_0(X52)|~v2_pre_topc(X52)|~l1_pre_topc(X52)|(v2_struct_0(X53)|~m1_pre_topc(X53,X51)|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X53),u1_struct_0(X52))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X53),u1_struct_0(X52))))|r2_funct_2(u1_struct_0(X53),u1_struct_0(X52),X54,k3_tmap_1(X51,X52,X53,X53,X54)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.21/0.51  fof(c_0_69, plain, ![X42, X43]:(~l1_pre_topc(X42)|(~m1_pre_topc(X43,X42)|m1_subset_1(u1_struct_0(X43),k1_zfmisc_1(u1_struct_0(X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.21/0.51  cnf(c_0_70, plain, (r2_hidden(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X3))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.51  cnf(c_0_71, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_72, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_73, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_74, plain, (m1_subset_1(esk1_5(X1,X2,X3,X4,X5),u1_struct_0(X2))|r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X3,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.51  cnf(c_0_75, negated_conjecture, (X1=k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~v1_funct_2(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.21/0.51  cnf(c_0_76, negated_conjecture, (v1_funct_1(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.21/0.51  cnf(c_0_77, negated_conjecture, (v1_funct_2(k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(spm,[status(thm)],[c_0_67, c_0_66])).
% 0.21/0.51  cnf(c_0_78, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.21/0.51  fof(c_0_79, plain, ![X9, X10, X11]:(~r2_hidden(X9,X10)|~m1_subset_1(X10,k1_zfmisc_1(X11))|m1_subset_1(X9,X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.51  cnf(c_0_80, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.21/0.51  cnf(c_0_81, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)|r2_hidden(esk1_5(esk2_0,X1,esk3_0,X2,esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_28]), c_0_29]), c_0_72]), c_0_73])]), c_0_43]), c_0_30])).
% 0.21/0.51  cnf(c_0_82, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)|m1_subset_1(esk1_5(esk2_0,X1,esk3_0,X2,esk4_0),u1_struct_0(X1))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_71]), c_0_28]), c_0_29]), c_0_72]), c_0_73])]), c_0_43]), c_0_30])).
% 0.21/0.51  cnf(c_0_83, negated_conjecture, (X1=k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))|~m1_pre_topc(esk3_0,esk3_0)|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.21/0.51  cnf(c_0_84, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(X1,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_38]), c_0_28]), c_0_29]), c_0_41]), c_0_42])]), c_0_43]), c_0_30])).
% 0.21/0.51  cnf(c_0_85, plain, (r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)|v2_struct_0(X4)|v2_struct_0(X1)|v2_struct_0(X2)|k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X2,X1,X4,X3,X5))!=k1_funct_1(X5,esk1_5(X2,X1,X4,X3,X5))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.21/0.51  cnf(c_0_86, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.21/0.51  cnf(c_0_87, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_27]), c_0_28])])).
% 0.21/0.51  cnf(c_0_88, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_38]), c_0_55]), c_0_66]), c_0_39]), c_0_40]), c_0_41]), c_0_42])]), c_0_43])).
% 0.21/0.51  fof(c_0_89, plain, ![X12, X13, X14, X15]:(v1_xboole_0(X12)|~v1_funct_1(X14)|~v1_funct_2(X14,X12,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|~m1_subset_1(X15,X12)|k3_funct_2(X12,X13,X14,X15)=k1_funct_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).
% 0.21/0.51  cnf(c_0_90, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_38]), c_0_55]), c_0_66]), c_0_39]), c_0_40]), c_0_41]), c_0_42])]), c_0_43])).
% 0.21/0.51  cnf(c_0_91, negated_conjecture, (X1=k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))|~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),X1,k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))|~v1_funct_2(X1,u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_47]), c_0_39])])).
% 0.21/0.51  cnf(c_0_92, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_27]), c_0_28]), c_0_29])]), c_0_30])).
% 0.21/0.51  cnf(c_0_93, negated_conjecture, (v2_struct_0(X1)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tmap_1(X1,esk2_0,X2,esk3_0),esk4_0)|k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))!=k1_funct_1(esk4_0,esk1_5(esk2_0,X1,esk3_0,X2,esk4_0))|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_71]), c_0_28]), c_0_29]), c_0_72]), c_0_73])]), c_0_43]), c_0_30])).
% 0.21/0.51  cnf(c_0_94, negated_conjecture, (m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_86, c_0_87])).
% 0.21/0.51  cnf(c_0_95, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)|r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_47]), c_0_39])])).
% 0.21/0.51  cnf(c_0_96, plain, (v1_xboole_0(X1)|k3_funct_2(X1,X3,X2,X4)=k1_funct_1(X2,X4)|~v1_funct_1(X2)|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))|~m1_subset_1(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_89])).
% 0.21/0.51  cnf(c_0_97, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_47]), c_0_39])])).
% 0.21/0.51  cnf(c_0_98, negated_conjecture, (k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0))=k4_tmap_1(esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_41]), c_0_42]), c_0_38])])).
% 0.21/0.51  cnf(c_0_99, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_100, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)|k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))!=k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_38]), c_0_55]), c_0_66]), c_0_39]), c_0_40]), c_0_41]), c_0_42])]), c_0_43])).
% 0.21/0.51  cnf(c_0_101, negated_conjecture, (X1=k1_funct_1(esk4_0,X1)|~m1_subset_1(X1,u1_struct_0(esk2_0))|~r2_hidden(X1,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.51  cnf(c_0_102, negated_conjecture, (r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)|m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.21/0.51  fof(c_0_103, plain, ![X25]:(v2_struct_0(X25)|~l1_struct_0(X25)|~v1_xboole_0(u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.21/0.51  cnf(c_0_104, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),X1)=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),X1)|v1_xboole_0(u1_struct_0(esk3_0))|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_38]), c_0_42])]), c_0_41])])).
% 0.21/0.51  cnf(c_0_105, negated_conjecture, (m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_98]), c_0_99])).
% 0.21/0.51  cnf(c_0_106, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))!=k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))|~m1_pre_topc(esk3_0,esk3_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_98]), c_0_99])).
% 0.21/0.51  cnf(c_0_107, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk2_0,esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0)),esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_95]), c_0_102])).
% 0.21/0.51  cnf(c_0_108, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.21/0.51  cnf(c_0_109, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))|v1_xboole_0(u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_104, c_0_105])).
% 0.21/0.51  fof(c_0_110, plain, ![X22]:(~l1_pre_topc(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.51  fof(c_0_111, plain, ![X58, X59, X60]:(v2_struct_0(X58)|~v2_pre_topc(X58)|~l1_pre_topc(X58)|(v2_struct_0(X59)|~m1_pre_topc(X59,X58)|(~m1_subset_1(X60,u1_struct_0(X58))|(~r2_hidden(X60,u1_struct_0(X59))|k1_funct_1(k4_tmap_1(X58,X59),X60)=X60)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t95_tmap_1])])])])).
% 0.21/0.51  cnf(c_0_112, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))!=k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_47]), c_0_39])])).
% 0.21/0.51  cnf(c_0_113, negated_conjecture, (k1_funct_1(esk4_0,esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_107, c_0_98]), c_0_99])).
% 0.21/0.51  cnf(c_0_114, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))|~l1_struct_0(esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_43])).
% 0.21/0.51  cnf(c_0_115, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_110])).
% 0.21/0.51  cnf(c_0_116, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k1_funct_1(k4_tmap_1(X1,X2),X3)=X3|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_111])).
% 0.21/0.51  cnf(c_0_117, negated_conjecture, (r2_hidden(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_98]), c_0_99])).
% 0.21/0.51  cnf(c_0_118, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))!=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_112, c_0_113])).
% 0.21/0.51  cnf(c_0_119, negated_conjecture, (k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_39])])).
% 0.21/0.51  cnf(c_0_120, negated_conjecture, (k1_funct_1(k4_tmap_1(X1,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)|v2_struct_0(X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~v2_pre_topc(X1)|~m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_43])).
% 0.21/0.51  cnf(c_0_121, negated_conjecture, (m1_subset_1(esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_102, c_0_98]), c_0_99])).
% 0.21/0.51  cnf(c_0_122, negated_conjecture, (k1_funct_1(k4_tmap_1(esk2_0,esk3_0),esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0))!=esk1_5(esk2_0,esk3_0,esk3_0,k4_tmap_1(esk2_0,esk3_0),esk4_0)), inference(rw,[status(thm)],[c_0_118, c_0_119])).
% 0.21/0.51  cnf(c_0_123, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_121]), c_0_27]), c_0_28]), c_0_29])]), c_0_122]), c_0_30]), ['proof']).
% 0.21/0.51  # SZS output end CNFRefutation
% 0.21/0.51  # Proof object total steps             : 124
% 0.21/0.51  # Proof object clause steps            : 87
% 0.21/0.51  # Proof object formula steps           : 37
% 0.21/0.51  # Proof object conjectures             : 66
% 0.21/0.51  # Proof object clause conjectures      : 63
% 0.21/0.51  # Proof object formula conjectures     : 3
% 0.21/0.51  # Proof object initial clauses used    : 33
% 0.21/0.51  # Proof object initial formulas used   : 18
% 0.21/0.51  # Proof object generating inferences   : 45
% 0.21/0.51  # Proof object simplifying inferences  : 175
% 0.21/0.51  # Training examples: 0 positive, 0 negative
% 0.21/0.51  # Parsed axioms                        : 19
% 0.21/0.51  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.51  # Initial clauses                      : 35
% 0.21/0.51  # Removed in clause preprocessing      : 0
% 0.21/0.51  # Initial clauses in saturation        : 35
% 0.21/0.51  # Processed clauses                    : 713
% 0.21/0.51  # ...of these trivial                  : 10
% 0.21/0.51  # ...subsumed                          : 96
% 0.21/0.51  # ...remaining for further processing  : 607
% 0.21/0.51  # Other redundant clauses eliminated   : 1
% 0.21/0.51  # Clauses deleted for lack of memory   : 0
% 0.21/0.51  # Backward-subsumed                    : 113
% 0.21/0.51  # Backward-rewritten                   : 144
% 0.21/0.51  # Generated clauses                    : 894
% 0.21/0.51  # ...of the previous two non-trivial   : 952
% 0.21/0.51  # Contextual simplify-reflections      : 34
% 0.21/0.51  # Paramodulations                      : 893
% 0.21/0.51  # Factorizations                       : 0
% 0.21/0.51  # Equation resolutions                 : 1
% 0.21/0.51  # Propositional unsat checks           : 0
% 0.21/0.51  #    Propositional check models        : 0
% 0.21/0.51  #    Propositional check unsatisfiable : 0
% 0.21/0.51  #    Propositional clauses             : 0
% 0.21/0.51  #    Propositional clauses after purity: 0
% 0.21/0.51  #    Propositional unsat core size     : 0
% 0.21/0.51  #    Propositional preprocessing time  : 0.000
% 0.21/0.51  #    Propositional encoding time       : 0.000
% 0.21/0.51  #    Propositional solver time         : 0.000
% 0.21/0.51  #    Success case prop preproc time    : 0.000
% 0.21/0.51  #    Success case prop encoding time   : 0.000
% 0.21/0.51  #    Success case prop solver time     : 0.000
% 0.21/0.51  # Current number of processed clauses  : 314
% 0.21/0.51  #    Positive orientable unit clauses  : 58
% 0.21/0.51  #    Positive unorientable unit clauses: 0
% 0.21/0.51  #    Negative unit clauses             : 4
% 0.21/0.51  #    Non-unit-clauses                  : 252
% 0.21/0.51  # Current number of unprocessed clauses: 234
% 0.21/0.51  # ...number of literals in the above   : 1389
% 0.21/0.51  # Current number of archived formulas  : 0
% 0.21/0.51  # Current number of archived clauses   : 292
% 0.21/0.51  # Clause-clause subsumption calls (NU) : 31087
% 0.21/0.51  # Rec. Clause-clause subsumption calls : 4077
% 0.21/0.51  # Non-unit clause-clause subsumptions  : 237
% 0.21/0.51  # Unit Clause-clause subsumption calls : 1241
% 0.21/0.51  # Rewrite failures with RHS unbound    : 0
% 0.21/0.51  # BW rewrite match attempts            : 332
% 0.21/0.51  # BW rewrite match successes           : 32
% 0.21/0.51  # Condensation attempts                : 0
% 0.21/0.51  # Condensation successes               : 0
% 0.21/0.51  # Termbank termtop insertions          : 53594
% 0.21/0.51  
% 0.21/0.51  # -------------------------------------------------
% 0.21/0.51  # User time                : 0.168 s
% 0.21/0.51  # System time              : 0.003 s
% 0.21/0.51  # Total time               : 0.171 s
% 0.21/0.51  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
