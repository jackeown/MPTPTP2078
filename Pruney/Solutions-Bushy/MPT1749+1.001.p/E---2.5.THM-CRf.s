%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1749+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:42 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   68 (1102 expanded)
%              Number of clauses        :   47 ( 384 expanded)
%              Number of leaves         :   10 ( 268 expanded)
%              Depth                    :   13
%              Number of atoms          :  321 (11476 expanded)
%              Number of equality atoms :   28 ( 658 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_tmap_1,conjecture,(
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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t173_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

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

fof(symmetry_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
       => r2_funct_2(X1,X2,X4,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r2_funct_2)).

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
    inference(assume_negation,[status(cth)],[t59_tmap_1])).

fof(c_0_11,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_pre_topc(X21,X20)
      | l1_pre_topc(X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_12,negated_conjecture,(
    ! [X47] :
      ( ~ v2_struct_0(esk2_0)
      & v2_pre_topc(esk2_0)
      & l1_pre_topc(esk2_0)
      & ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & ~ v2_struct_0(esk4_0)
      & m1_pre_topc(esk4_0,esk3_0)
      & v1_funct_1(esk5_0)
      & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X47,u1_struct_0(esk3_0))
        | ~ r2_hidden(X47,u1_struct_0(esk4_0))
        | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X47) = k1_funct_1(esk6_0,X47) )
      & ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X22] :
      ( v2_struct_0(X22)
      | ~ l1_struct_0(X22)
      | ~ v1_xboole_0(u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_14,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_15,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_23,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( ( m1_subset_1(esk1_5(X31,X32,X33,X34,X35),X31)
        | k2_partfun1(X31,X32,X33,X34) = X35
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X34,X32)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X31))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32)
        | v1_xboole_0(X31) )
      & ( r2_hidden(esk1_5(X31,X32,X33,X34,X35),X34)
        | k2_partfun1(X31,X32,X33,X34) = X35
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X34,X32)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X31))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32)
        | v1_xboole_0(X31) )
      & ( k3_funct_2(X31,X32,X33,esk1_5(X31,X32,X33,X34,X35)) != k1_funct_1(X35,esk1_5(X31,X32,X33,X34,X35))
        | k2_partfun1(X31,X32,X33,X34) = X35
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X34,X32)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X32)))
        | v1_xboole_0(X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(X31))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
        | v1_xboole_0(X32)
        | v1_xboole_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

cnf(c_0_24,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_22])).

fof(c_0_28,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_30,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X3,esk1_5(X1,X2,X3,X4,X5)) != k1_funct_1(X5,esk1_5(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_25])])).

cnf(c_0_35,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_19]),c_0_27])])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_17])).

fof(c_0_39,plain,(
    ! [X39,X40,X41] :
      ( ~ r2_hidden(X39,X40)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X41))
      | m1_subset_1(X39,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_40,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0)) = esk6_0
    | v1_xboole_0(X1)
    | k3_funct_2(X1,u1_struct_0(esk2_0),X2,esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0)) != k1_funct_1(esk6_0,esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_16]),c_0_17])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_38])])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_5(X1,X2,X3,X4,X5),X4)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0
    | k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0)) != k1_funct_1(esk6_0,esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_42])).

fof(c_0_51,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ v1_funct_1(X29)
      | ~ v1_funct_2(X29,X27,X28)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,X27,X28)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | ~ r2_funct_2(X27,X28,X29,X30)
      | r2_funct_2(X27,X28,X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r2_funct_2])])).

fof(c_0_52,plain,(
    ! [X7,X8,X9,X10] :
      ( v2_struct_0(X7)
      | ~ v2_pre_topc(X7)
      | ~ l1_pre_topc(X7)
      | v2_struct_0(X8)
      | ~ v2_pre_topc(X8)
      | ~ l1_pre_topc(X8)
      | ~ v1_funct_1(X9)
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ m1_pre_topc(X10,X7)
      | k2_tmap_1(X7,X8,X9,X10) = k2_partfun1(u1_struct_0(X7),u1_struct_0(X8),X9,u1_struct_0(X10)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_53,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0)) = esk6_0
    | r2_hidden(esk1_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0))
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk4_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_31]),c_0_32]),c_0_33])]),c_0_34]),c_0_35])).

cnf(c_0_54,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0
    | ~ r2_hidden(esk1_5(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0),esk6_0),u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_56,plain,
    ( r2_funct_2(X2,X3,X4,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_funct_2(X2,X3,X1,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = esk6_0 ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_41]),c_0_42]),c_0_43]),c_0_44])]),c_0_45]),c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_61,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ r2_funct_2(X23,X24,X25,X26)
        | X25 = X26
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X23,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X25 != X26
        | r2_funct_2(X23,X24,X25,X26)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,X23,X24)
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0))
    | ~ m1_subset_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_63,negated_conjecture,
    ( k2_tmap_1(esk3_0,esk2_0,esk5_0,esk4_0) = esk6_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_16]),c_0_41]),c_0_43]),c_0_44]),c_0_22]),c_0_17]),c_0_59]),c_0_60])]),c_0_26]),c_0_29])).

cnf(c_0_64,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_63]),c_0_31]),c_0_63]),c_0_32]),c_0_63]),c_0_33])])).

cnf(c_0_66,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_31]),c_0_32]),c_0_33])]),
    [proof]).

%------------------------------------------------------------------------------
