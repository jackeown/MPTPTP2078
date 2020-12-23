%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:20 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  125 (84646 expanded)
%              Number of clauses        :   96 (26630 expanded)
%              Number of leaves         :   14 (20928 expanded)
%              Depth                    :   22
%              Number of atoms          :  598 (709744 expanded)
%              Number of equality atoms :   82 (17257 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   68 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> ( v1_funct_1(k7_tmap_1(X1,X2))
              & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
              & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
              & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t55_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => ( v5_pre_topc(X3,X1,X2)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( v3_pre_topc(X4,X2)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(d10_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(t105_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
             => ( X3 = X2
               => v3_pre_topc(X3,k6_tmap_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> ( v1_funct_1(k7_tmap_1(X1,X2))
                & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
                & v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2))
                & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t113_tmap_1])).

fof(c_0_15,plain,(
    ! [X33,X34] :
      ( ( u1_struct_0(k6_tmap_1(X33,X34)) = u1_struct_0(X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( u1_pre_topc(k6_tmap_1(X33,X34)) = k5_tmap_1(X33,X34)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ v3_pre_topc(esk3_0,esk2_0)
      | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) )
    & ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
      | v3_pre_topc(esk3_0,esk2_0) )
    & ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))
      | v3_pre_topc(esk3_0,esk2_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).

fof(c_0_17,plain,(
    ! [X26,X27] :
      ( ( v1_pre_topc(k6_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( v2_pre_topc(k6_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) )
      & ( l1_pre_topc(k6_tmap_1(X26,X27))
        | v2_struct_0(X26)
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_18,plain,(
    ! [X31,X32] :
      ( ( ~ r2_hidden(X32,u1_pre_topc(X31))
        | u1_pre_topc(X31) = k5_tmap_1(X31,X32)
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( u1_pre_topc(X31) != k5_tmap_1(X31,X32)
        | r2_hidden(X32,u1_pre_topc(X31))
        | ~ m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))
        | v2_struct_0(X31)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

fof(c_0_19,plain,(
    ! [X16,X17] :
      ( ( ~ v3_pre_topc(X17,X16)
        | r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(X17,u1_pre_topc(X16))
        | v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_20,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_28,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ v5_pre_topc(X21,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ v3_pre_topc(X22,X20)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X19)
        | k2_struct_0(X20) = k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk1_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | v5_pre_topc(X21,X19,X20)
        | k2_struct_0(X20) = k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(esk1_3(X19,X20,X21),X20)
        | v5_pre_topc(X21,X19,X20)
        | k2_struct_0(X20) = k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk1_3(X19,X20,X21)),X19)
        | v5_pre_topc(X21,X19,X20)
        | k2_struct_0(X20) = k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ v5_pre_topc(X21,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ v3_pre_topc(X22,X20)
        | v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X19)
        | k2_struct_0(X19) != k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk1_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X20)))
        | v5_pre_topc(X21,X19,X20)
        | k2_struct_0(X19) != k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(esk1_3(X19,X20,X21),X20)
        | v5_pre_topc(X21,X19,X20)
        | k2_struct_0(X19) != k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) )
      & ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk1_3(X19,X20,X21)),X19)
        | v5_pre_topc(X21,X19,X20)
        | k2_struct_0(X19) != k1_xboole_0
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_pre_topc(X20)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).

fof(c_0_29,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))
      | k7_tmap_1(X24,X25) = k6_partfun1(u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).

fof(c_0_30,plain,(
    ! [X28,X29] :
      ( ( v1_funct_1(k7_tmap_1(X28,X29))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) )
      & ( v1_funct_2(k7_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k6_tmap_1(X28,X29)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) )
      & ( m1_subset_1(k7_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k6_tmap_1(X28,X29)))))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) = k5_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(k6_tmap_1(esk2_0,esk3_0)) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0)
    | ~ r2_hidden(esk3_0,u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_36,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | k2_struct_0(X3) = k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(X13))
      | k8_relset_1(X13,X13,k6_partfun1(X13),X14) = X14 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

cnf(c_0_38,plain,
    ( v2_struct_0(X1)
    | k7_tmap_1(X1,X2) = k6_partfun1(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,k5_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_43,negated_conjecture,
    ( k5_tmap_1(esk2_0,esk3_0) = u1_pre_topc(esk2_0)
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_31]),c_0_23]),c_0_21])])).

fof(c_0_44,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | ~ m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X35,X36))))
      | X37 != X36
      | v3_pre_topc(X37,k6_tmap_1(X35,X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).

cnf(c_0_45,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_33])])).

cnf(c_0_46,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( k6_partfun1(u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_34]),c_0_22]),c_0_23]),c_0_21])]),c_0_24])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_22]),c_0_23])]),c_0_24]),c_0_34])).

cnf(c_0_51,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,u1_pre_topc(esk2_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_53,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X3,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | X3 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_54,negated_conjecture,
    ( ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ v1_funct_1(k7_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_55,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_56,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_57,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_47]),c_0_49]),c_0_23]),c_0_47]),c_0_50])])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23])])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | v3_pre_topc(X2,k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_53])).

fof(c_0_61,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_49])])).

cnf(c_0_63,plain,
    ( v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X2) = k1_xboole_0
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_64,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_33])])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_34]),c_0_33])])).

cnf(c_0_66,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_34]),c_0_22]),c_0_23]),c_0_21])]),c_0_24])).

fof(c_0_68,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_34]),c_0_34]),c_0_48])])).

cnf(c_0_71,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_34]),c_0_33])])).

cnf(c_0_72,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_50]),c_0_48]),c_0_49]),c_0_23])])).

cnf(c_0_73,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_50]),c_0_48]),c_0_49]),c_0_23])])).

cnf(c_0_74,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_21])])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_76,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_69])).

fof(c_0_77,plain,(
    ! [X15] :
      ( ~ l1_struct_0(X15)
      | k2_struct_0(X15) = u1_struct_0(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_78,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_50])])).

cnf(c_0_80,negated_conjecture,
    ( k7_tmap_1(esk2_0,X1) = k7_tmap_1(esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_47]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_81,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)
    | ~ m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_47]),c_0_49]),c_0_47]),c_0_23]),c_0_47]),c_0_50]),c_0_47])])).

cnf(c_0_82,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_72]),c_0_73]),c_0_74])).

cnf(c_0_83,plain,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v3_pre_topc(X4,X3)
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_84,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_85,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_86,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_88,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0
    | v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_73])).

cnf(c_0_89,negated_conjecture,
    ( v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_34]),c_0_33])])).

cnf(c_0_90,plain,
    ( k7_tmap_1(X1,u1_struct_0(X1)) = k6_partfun1(u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_84])).

cnf(c_0_91,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k2_struct_0(k6_tmap_1(esk2_0,esk3_0)) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_21])]),c_0_74])).

cnf(c_0_93,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_47]),c_0_49]),c_0_23]),c_0_47]),c_0_50])])).

cnf(c_0_94,negated_conjecture,
    ( k7_tmap_1(esk2_0,u1_struct_0(esk2_0)) = k7_tmap_1(esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_22]),c_0_47]),c_0_23])]),c_0_24])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_34]),c_0_33])])).

cnf(c_0_96,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_80])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | u1_struct_0(esk2_0) != k1_xboole_0
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_91]),c_0_23])])).

cnf(c_0_98,negated_conjecture,
    ( k7_tmap_1(esk2_0,esk3_0) = k7_tmap_1(esk2_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_96,c_0_95])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_95])).

cnf(c_0_101,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_102,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_95]),c_0_95])]),c_0_98])).

cnf(c_0_103,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_98]),c_0_100])])).

cnf(c_0_104,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_59,c_0_95])).

cnf(c_0_105,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_106,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_34]),c_0_33])])).

cnf(c_0_107,negated_conjecture,
    ( v3_pre_topc(X1,esk2_0)
    | ~ v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_104])).

cnf(c_0_108,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_34]),c_0_33])])).

cnf(c_0_109,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | k2_struct_0(X1) != k1_xboole_0
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_110,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_50]),c_0_48]),c_0_49]),c_0_23])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | ~ v3_pre_topc(esk3_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_79,c_0_98])).

cnf(c_0_112,negated_conjecture,
    ( v3_pre_topc(esk3_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_67]),c_0_100])])).

cnf(c_0_113,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | k2_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_50]),c_0_48]),c_0_49]),c_0_23])])).

cnf(c_0_114,negated_conjecture,
    ( v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(X2) != k1_xboole_0
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1)),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_34]),c_0_33])])).

cnf(c_0_115,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_91]),c_0_23])])).

cnf(c_0_116,negated_conjecture,
    ( ~ v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_112])])).

cnf(c_0_117,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_91]),c_0_23])])).

cnf(c_0_118,negated_conjecture,
    ( v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))
    | k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_46]),c_0_47]),c_0_47]),c_0_48]),c_0_47]),c_0_49]),c_0_47]),c_0_23]),c_0_47]),c_0_50]),c_0_47])]),c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k6_tmap_1(esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115,c_0_95])]),c_0_98]),c_0_98]),c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117,c_0_95]),c_0_95])]),c_0_98]),c_0_98]),c_0_116])).

cnf(c_0_121,negated_conjecture,
    ( k2_struct_0(esk2_0) != k1_xboole_0
    | ~ v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118,c_0_98]),c_0_98]),c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_119]),c_0_120])])).

cnf(c_0_123,negated_conjecture,
    ( k2_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121,c_0_122])])).

cnf(c_0_124,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_91]),c_0_95]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:07:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.59/0.84  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.59/0.84  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.59/0.84  #
% 0.59/0.84  # Preprocessing time       : 0.038 s
% 0.59/0.84  
% 0.59/0.84  # Proof found!
% 0.59/0.84  # SZS status Theorem
% 0.59/0.84  # SZS output start CNFRefutation
% 0.59/0.84  fof(t113_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_tmap_1)).
% 0.59/0.84  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.59/0.84  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.59/0.84  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.59/0.84  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.59/0.84  fof(t55_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v3_pre_topc(X4,X2)=>v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_2)).
% 0.59/0.84  fof(d10_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_tmap_1)).
% 0.59/0.84  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.59/0.84  fof(t171_funct_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_2)).
% 0.59/0.84  fof(t105_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))=>(X3=X2=>v3_pre_topc(X3,k6_tmap_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_tmap_1)).
% 0.59/0.84  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.59/0.84  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.59/0.84  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.59/0.84  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.59/0.84  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>(((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&v5_pre_topc(k7_tmap_1(X1,X2),X1,k6_tmap_1(X1,X2)))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))))))), inference(assume_negation,[status(cth)],[t113_tmap_1])).
% 0.59/0.84  fof(c_0_15, plain, ![X33, X34]:((u1_struct_0(k6_tmap_1(X33,X34))=u1_struct_0(X33)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(u1_pre_topc(k6_tmap_1(X33,X34))=k5_tmap_1(X33,X34)|~m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.59/0.84  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~v3_pre_topc(esk3_0,esk2_0)|(~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))))&((((v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0))&(v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|v3_pre_topc(esk3_0,esk2_0)))&(v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)))&(m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))|v3_pre_topc(esk3_0,esk2_0)))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])).
% 0.59/0.84  fof(c_0_17, plain, ![X26, X27]:(((v1_pre_topc(k6_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))&(v2_pre_topc(k6_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26))))))&(l1_pre_topc(k6_tmap_1(X26,X27))|(v2_struct_0(X26)|~v2_pre_topc(X26)|~l1_pre_topc(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X26)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.59/0.84  fof(c_0_18, plain, ![X31, X32]:((~r2_hidden(X32,u1_pre_topc(X31))|u1_pre_topc(X31)=k5_tmap_1(X31,X32)|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(u1_pre_topc(X31)!=k5_tmap_1(X31,X32)|r2_hidden(X32,u1_pre_topc(X31))|~m1_subset_1(X32,k1_zfmisc_1(u1_struct_0(X31)))|(v2_struct_0(X31)|~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.59/0.84  fof(c_0_19, plain, ![X16, X17]:((~v3_pre_topc(X17,X16)|r2_hidden(X17,u1_pre_topc(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(~r2_hidden(X17,u1_pre_topc(X16))|v3_pre_topc(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.59/0.84  cnf(c_0_20, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.84  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.84  cnf(c_0_22, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.84  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.84  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.84  cnf(c_0_25, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.59/0.84  cnf(c_0_26, plain, (u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.59/0.84  cnf(c_0_27, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.59/0.84  fof(c_0_28, plain, ![X19, X20, X21, X22]:(((~v5_pre_topc(X21,X19,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~v3_pre_topc(X22,X20)|v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X19)))|k2_struct_0(X20)=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&((m1_subset_1(esk1_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|v5_pre_topc(X21,X19,X20)|k2_struct_0(X20)=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&((v3_pre_topc(esk1_3(X19,X20,X21),X20)|v5_pre_topc(X21,X19,X20)|k2_struct_0(X20)=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk1_3(X19,X20,X21)),X19)|v5_pre_topc(X21,X19,X20)|k2_struct_0(X20)=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19)))))&((~v5_pre_topc(X21,X19,X20)|(~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X20)))|(~v3_pre_topc(X22,X20)|v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X19)))|k2_struct_0(X19)!=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&((m1_subset_1(esk1_3(X19,X20,X21),k1_zfmisc_1(u1_struct_0(X20)))|v5_pre_topc(X21,X19,X20)|k2_struct_0(X19)!=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&((v3_pre_topc(esk1_3(X19,X20,X21),X20)|v5_pre_topc(X21,X19,X20)|k2_struct_0(X19)!=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19))&(~v3_pre_topc(k8_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk1_3(X19,X20,X21)),X19)|v5_pre_topc(X21,X19,X20)|k2_struct_0(X19)!=k1_xboole_0|(~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20)))))|~l1_pre_topc(X20)|~l1_pre_topc(X19)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_tops_2])])])])])).
% 0.59/0.84  fof(c_0_29, plain, ![X24, X25]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(~m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X24)))|k7_tmap_1(X24,X25)=k6_partfun1(u1_struct_0(X24)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d10_tmap_1])])])])).
% 0.59/0.84  fof(c_0_30, plain, ![X28, X29]:(((v1_funct_1(k7_tmap_1(X28,X29))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))))&(v1_funct_2(k7_tmap_1(X28,X29),u1_struct_0(X28),u1_struct_0(k6_tmap_1(X28,X29)))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28))))))&(m1_subset_1(k7_tmap_1(X28,X29),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(k6_tmap_1(X28,X29)))))|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|~m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.59/0.84  cnf(c_0_31, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.59/0.84  cnf(c_0_32, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk2_0,esk3_0))=k5_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_33, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_34, negated_conjecture, (u1_struct_0(k6_tmap_1(esk2_0,esk3_0))=u1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_35, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)|~r2_hidden(esk3_0,u1_pre_topc(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_36, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|k2_struct_0(X3)=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  fof(c_0_37, plain, ![X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(X13))|k8_relset_1(X13,X13,k6_partfun1(X13),X14)=X14), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).
% 0.59/0.84  cnf(c_0_38, plain, (v2_struct_0(X1)|k7_tmap_1(X1,X2)=k6_partfun1(u1_struct_0(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.59/0.84  cnf(c_0_39, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.59/0.84  cnf(c_0_40, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.59/0.84  cnf(c_0_41, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.59/0.84  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,k5_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])])).
% 0.59/0.84  cnf(c_0_43, negated_conjecture, (k5_tmap_1(esk2_0,esk3_0)=u1_pre_topc(esk2_0)|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_31]), c_0_23]), c_0_21])])).
% 0.59/0.84  fof(c_0_44, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(~m1_subset_1(X36,k1_zfmisc_1(u1_struct_0(X35)))|(~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X35,X36))))|(X37!=X36|v3_pre_topc(X37,k6_tmap_1(X35,X36)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t105_tmap_1])])])])).
% 0.59/0.84  cnf(c_0_45, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_46, plain, (k8_relset_1(X2,X2,k6_partfun1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.59/0.84  cnf(c_0_47, negated_conjecture, (k6_partfun1(u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_48, negated_conjecture, (v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_34]), c_0_22]), c_0_23]), c_0_21])]), c_0_24])).
% 0.59/0.84  cnf(c_0_49, negated_conjecture, (v1_funct_1(k7_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_21]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_50, negated_conjecture, (m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_21]), c_0_22]), c_0_23])]), c_0_24]), c_0_34])).
% 0.59/0.84  cnf(c_0_51, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.59/0.84  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,u1_pre_topc(esk2_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.59/0.84  cnf(c_0_53, plain, (v2_struct_0(X1)|v3_pre_topc(X3,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|X3!=X2), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.59/0.84  cnf(c_0_54, negated_conjecture, (~v3_pre_topc(esk3_0,esk2_0)|~v1_funct_1(k7_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.84  cnf(c_0_55, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_56, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_57, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(X1,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_47]), c_0_49]), c_0_23]), c_0_47]), c_0_50])])).
% 0.59/0.84  cnf(c_0_58, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.59/0.84  cnf(c_0_59, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_23])])).
% 0.59/0.84  cnf(c_0_60, plain, (v2_struct_0(X1)|v3_pre_topc(X2,k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X1,X2))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(er,[status(thm)],[c_0_53])).
% 0.59/0.84  fof(c_0_61, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.59/0.84  cnf(c_0_62, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(k7_tmap_1(esk2_0,esk3_0),u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(k6_tmap_1(esk2_0,esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_49])])).
% 0.59/0.84  cnf(c_0_63, plain, (v5_pre_topc(X3,X1,X2)|k2_struct_0(X2)=k1_xboole_0|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_64, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_65, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_66, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 0.59/0.84  cnf(c_0_67, negated_conjecture, (v3_pre_topc(esk3_0,k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_34]), c_0_22]), c_0_23]), c_0_21])]), c_0_24])).
% 0.59/0.84  fof(c_0_68, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.59/0.84  cnf(c_0_69, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.59/0.84  cnf(c_0_70, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(k7_tmap_1(esk2_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_34]), c_0_34]), c_0_48])])).
% 0.59/0.84  cnf(c_0_71, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_72, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_50]), c_0_48]), c_0_49]), c_0_23])])).
% 0.59/0.84  cnf(c_0_73, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_50]), c_0_48]), c_0_49]), c_0_23])])).
% 0.59/0.84  cnf(c_0_74, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_21])])).
% 0.59/0.84  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.59/0.84  cnf(c_0_76, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_69])).
% 0.59/0.84  fof(c_0_77, plain, ![X15]:(~l1_struct_0(X15)|k2_struct_0(X15)=u1_struct_0(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.59/0.84  fof(c_0_78, plain, ![X18]:(~l1_pre_topc(X18)|l1_struct_0(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.59/0.84  cnf(c_0_79, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_50])])).
% 0.59/0.84  cnf(c_0_80, negated_conjecture, (k7_tmap_1(esk2_0,X1)=k7_tmap_1(esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_47]), c_0_22]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_81, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)|~m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_47]), c_0_49]), c_0_47]), c_0_23]), c_0_47]), c_0_50]), c_0_47])])).
% 0.59/0.84  cnf(c_0_82, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_72]), c_0_73]), c_0_74])).
% 0.59/0.84  cnf(c_0_83, plain, (v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v3_pre_topc(X4,X3)|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_84, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.59/0.84  cnf(c_0_85, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.59/0.84  cnf(c_0_86, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.59/0.84  cnf(c_0_87, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.59/0.84  cnf(c_0_88, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0|v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_73])).
% 0.59/0.84  cnf(c_0_89, negated_conjecture, (v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),X1)|k2_struct_0(X1)!=k1_xboole_0|~v5_pre_topc(X2,X1,k6_tmap_1(esk2_0,esk3_0))|~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))|~v1_funct_1(X2)|~v3_pre_topc(X3,k6_tmap_1(esk2_0,esk3_0))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_90, plain, (k7_tmap_1(X1,u1_struct_0(X1))=k6_partfun1(u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_38, c_0_84])).
% 0.59/0.84  cnf(c_0_91, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.59/0.84  cnf(c_0_92, negated_conjecture, (k2_struct_0(k6_tmap_1(esk2_0,esk3_0))=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_21])]), c_0_74])).
% 0.59/0.84  cnf(c_0_93, negated_conjecture, (v3_pre_topc(X1,esk2_0)|k2_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_47]), c_0_49]), c_0_23]), c_0_47]), c_0_50])])).
% 0.59/0.84  cnf(c_0_94, negated_conjecture, (k7_tmap_1(esk2_0,u1_struct_0(esk2_0))=k7_tmap_1(esk2_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_22]), c_0_47]), c_0_23])]), c_0_24])).
% 0.59/0.84  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_96, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_58, c_0_80])).
% 0.59/0.84  cnf(c_0_97, negated_conjecture, (v3_pre_topc(X1,esk2_0)|u1_struct_0(esk2_0)!=k1_xboole_0|~v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_91]), c_0_23])])).
% 0.59/0.84  cnf(c_0_98, negated_conjecture, (k7_tmap_1(esk2_0,esk3_0)=k7_tmap_1(esk2_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_94, c_0_95])).
% 0.59/0.84  cnf(c_0_99, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,X1),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_96, c_0_95])).
% 0.59/0.84  cnf(c_0_100, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_21, c_0_95])).
% 0.59/0.84  cnf(c_0_101, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_102, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_97, c_0_95]), c_0_95])]), c_0_98])).
% 0.59/0.84  cnf(c_0_103, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_98]), c_0_100])])).
% 0.59/0.84  cnf(c_0_104, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_59, c_0_95])).
% 0.59/0.84  cnf(c_0_105, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_106, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_107, negated_conjecture, (v3_pre_topc(X1,esk2_0)|~v3_pre_topc(X1,k6_tmap_1(esk2_0,esk3_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_103]), c_0_104])).
% 0.59/0.84  cnf(c_0_108, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1),k1_zfmisc_1(u1_struct_0(esk2_0)))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_109, plain, (v5_pre_topc(X3,X1,X2)|~v3_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|k2_struct_0(X1)!=k1_xboole_0|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.59/0.84  cnf(c_0_110, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_50]), c_0_48]), c_0_49]), c_0_23])])).
% 0.59/0.84  cnf(c_0_111, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|~v3_pre_topc(esk3_0,esk2_0)), inference(rw,[status(thm)],[c_0_79, c_0_98])).
% 0.59/0.84  cnf(c_0_112, negated_conjecture, (v3_pre_topc(esk3_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_67]), c_0_100])])).
% 0.59/0.84  cnf(c_0_113, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))|k2_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_50]), c_0_48]), c_0_49]), c_0_23])])).
% 0.59/0.84  cnf(c_0_114, negated_conjecture, (v5_pre_topc(X1,X2,k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(X2)!=k1_xboole_0|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(esk2_0))|~v1_funct_1(X1)|~v3_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(esk2_0),X1,esk1_3(X2,k6_tmap_1(esk2_0,esk3_0),X1)),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_34]), c_0_33])])).
% 0.59/0.84  cnf(c_0_115, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k6_tmap_1(esk2_0,esk3_0))|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110, c_0_91]), c_0_23])])).
% 0.59/0.84  cnf(c_0_116, negated_conjecture, (~v5_pre_topc(k7_tmap_1(esk2_0,k1_xboole_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_112])])).
% 0.59/0.84  cnf(c_0_117, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113, c_0_91]), c_0_23])])).
% 0.59/0.84  cnf(c_0_118, negated_conjecture, (v5_pre_topc(k7_tmap_1(esk2_0,esk3_0),esk2_0,k6_tmap_1(esk2_0,esk3_0))|k2_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,esk3_0)),esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_46]), c_0_47]), c_0_47]), c_0_48]), c_0_47]), c_0_49]), c_0_47]), c_0_23]), c_0_47]), c_0_50]), c_0_47])]), c_0_113])).
% 0.59/0.84  cnf(c_0_119, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k6_tmap_1(esk2_0,esk3_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_115, c_0_95])]), c_0_98]), c_0_98]), c_0_116])).
% 0.59/0.84  cnf(c_0_120, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_117, c_0_95]), c_0_95])]), c_0_98]), c_0_98]), c_0_116])).
% 0.59/0.84  cnf(c_0_121, negated_conjecture, (k2_struct_0(esk2_0)!=k1_xboole_0|~v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_118, c_0_98]), c_0_98]), c_0_116])).
% 0.59/0.84  cnf(c_0_122, negated_conjecture, (v3_pre_topc(esk1_3(esk2_0,k6_tmap_1(esk2_0,esk3_0),k7_tmap_1(esk2_0,k1_xboole_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_119]), c_0_120])])).
% 0.59/0.84  cnf(c_0_123, negated_conjecture, (k2_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_121, c_0_122])])).
% 0.59/0.84  cnf(c_0_124, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_91]), c_0_95]), c_0_23])]), ['proof']).
% 0.59/0.84  # SZS output end CNFRefutation
% 0.59/0.84  # Proof object total steps             : 125
% 0.59/0.84  # Proof object clause steps            : 96
% 0.59/0.84  # Proof object formula steps           : 29
% 0.59/0.84  # Proof object conjectures             : 70
% 0.59/0.84  # Proof object clause conjectures      : 67
% 0.59/0.84  # Proof object formula conjectures     : 3
% 0.59/0.84  # Proof object initial clauses used    : 30
% 0.59/0.84  # Proof object initial formulas used   : 14
% 0.59/0.84  # Proof object generating inferences   : 50
% 0.59/0.84  # Proof object simplifying inferences  : 193
% 0.59/0.84  # Training examples: 0 positive, 0 negative
% 0.59/0.84  # Parsed axioms                        : 16
% 0.59/0.84  # Removed by relevancy pruning/SinE    : 0
% 0.59/0.84  # Initial clauses                      : 43
% 0.59/0.84  # Removed in clause preprocessing      : 0
% 0.59/0.84  # Initial clauses in saturation        : 43
% 0.59/0.84  # Processed clauses                    : 1981
% 0.59/0.84  # ...of these trivial                  : 30
% 0.59/0.84  # ...subsumed                          : 882
% 0.59/0.84  # ...remaining for further processing  : 1069
% 0.59/0.84  # Other redundant clauses eliminated   : 3
% 0.59/0.84  # Clauses deleted for lack of memory   : 0
% 0.59/0.84  # Backward-subsumed                    : 56
% 0.59/0.84  # Backward-rewritten                   : 534
% 0.59/0.84  # Generated clauses                    : 9647
% 0.59/0.84  # ...of the previous two non-trivial   : 9793
% 0.59/0.84  # Contextual simplify-reflections      : 258
% 0.59/0.84  # Paramodulations                      : 9641
% 0.59/0.84  # Factorizations                       : 0
% 0.59/0.84  # Equation resolutions                 : 3
% 0.59/0.84  # Propositional unsat checks           : 0
% 0.59/0.84  #    Propositional check models        : 0
% 0.59/0.84  #    Propositional check unsatisfiable : 0
% 0.59/0.84  #    Propositional clauses             : 0
% 0.59/0.84  #    Propositional clauses after purity: 0
% 0.59/0.84  #    Propositional unsat core size     : 0
% 0.59/0.84  #    Propositional preprocessing time  : 0.000
% 0.59/0.84  #    Propositional encoding time       : 0.000
% 0.59/0.84  #    Propositional solver time         : 0.000
% 0.59/0.84  #    Success case prop preproc time    : 0.000
% 0.59/0.84  #    Success case prop encoding time   : 0.000
% 0.59/0.84  #    Success case prop solver time     : 0.000
% 0.59/0.84  # Current number of processed clauses  : 473
% 0.59/0.84  #    Positive orientable unit clauses  : 35
% 0.59/0.84  #    Positive unorientable unit clauses: 0
% 0.59/0.84  #    Negative unit clauses             : 3
% 0.59/0.84  #    Non-unit-clauses                  : 435
% 0.59/0.84  # Current number of unprocessed clauses: 5160
% 0.59/0.84  # ...number of literals in the above   : 44536
% 0.59/0.84  # Current number of archived formulas  : 0
% 0.59/0.84  # Current number of archived clauses   : 593
% 0.59/0.84  # Clause-clause subsumption calls (NU) : 169009
% 0.59/0.84  # Rec. Clause-clause subsumption calls : 24223
% 0.59/0.84  # Non-unit clause-clause subsumptions  : 1185
% 0.59/0.84  # Unit Clause-clause subsumption calls : 1550
% 0.59/0.84  # Rewrite failures with RHS unbound    : 0
% 0.59/0.84  # BW rewrite match attempts            : 45
% 0.59/0.84  # BW rewrite match successes           : 14
% 0.59/0.84  # Condensation attempts                : 0
% 0.59/0.84  # Condensation successes               : 0
% 0.59/0.84  # Termbank termtop insertions          : 604999
% 0.59/0.84  
% 0.59/0.84  # -------------------------------------------------
% 0.59/0.84  # User time                : 0.489 s
% 0.59/0.84  # System time              : 0.012 s
% 0.59/0.84  # Total time               : 0.501 s
% 0.59/0.84  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
