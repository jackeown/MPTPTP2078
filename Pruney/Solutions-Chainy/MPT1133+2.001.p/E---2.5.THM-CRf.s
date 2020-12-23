%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:22 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  198 (9851522 expanded)
%              Number of clauses        :  171 (3730490 expanded)
%              Number of leaves         :   13 (2252990 expanded)
%              Depth                    :   43
%              Number of atoms          :  791 (86755147 expanded)
%              Number of equality atoms :  195 (14894960 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t63_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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

fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_pre_topc])).

fof(c_0_14,negated_conjecture,
    ( v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    & esk3_0 = esk4_0
    & ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) )
    & ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
      | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v5_pre_topc(X29,X27,X28)
        | v5_pre_topc(X30,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)),X28)
        | X29 != X30
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) )
      & ( ~ v5_pre_topc(X30,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)),X28)
        | v5_pre_topc(X29,X27,X28)
        | X29 != X30
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28))))
        | ~ v1_funct_1(X29)
        | ~ v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28)
        | ~ v2_pre_topc(X27)
        | ~ l1_pre_topc(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

fof(c_0_16,plain,(
    ! [X19,X20,X21] :
      ( ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X20 = k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X19 = k1_relset_1(X19,X20,X21)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X19 != k1_relset_1(X19,X20,X21)
        | v1_funct_2(X21,X19,X20)
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( ~ v1_funct_2(X21,X19,X20)
        | X21 = k1_xboole_0
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != k1_xboole_0
        | v1_funct_2(X21,X19,X20)
        | X19 = k1_xboole_0
        | X20 != k1_xboole_0
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk3_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_21,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_33,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_35,negated_conjecture,
    ( k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),esk3_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_25]),c_0_26])])).

cnf(c_0_36,plain,
    ( X1 = k1_relat_1(X2)
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_25]),c_0_30]),c_0_31]),c_0_32]),c_0_26])])).

cnf(c_0_38,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_18])).

fof(c_0_39,plain,(
    ! [X26] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))
        | ~ v2_pre_topc(X26)
        | ~ l1_pre_topc(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_34]),c_0_23])])).

cnf(c_0_42,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_35]),c_0_25])])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_25]),c_0_26])])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_45,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_47,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_48,plain,(
    ! [X23,X24] :
      ( ( v1_pre_topc(g1_pre_topc(X23,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))) )
      & ( l1_pre_topc(g1_pre_topc(X23,X24))
        | ~ m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_49,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ v5_pre_topc(X33,X31,X32)
        | v5_pre_topc(X34,X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))
        | X33 != X34
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) )
      & ( ~ v5_pre_topc(X34,X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))
        | v5_pre_topc(X33,X31,X32)
        | X33 != X34
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))))
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))))))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32))))
        | ~ v2_pre_topc(X32)
        | ~ l1_pre_topc(X32)
        | ~ v2_pre_topc(X31)
        | ~ l1_pre_topc(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_26])])).

cnf(c_0_51,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0)
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_43])).

cnf(c_0_53,plain,
    ( v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_55,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_56,plain,(
    ! [X25] :
      ( ~ l1_pre_topc(X25)
      | m1_subset_1(u1_pre_topc(X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_57,plain,
    ( v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_60,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_62,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_63,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_25,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_26,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_25]),c_0_30]),c_0_31]),c_0_32]),c_0_26])])).

cnf(c_0_69,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_61])).

cnf(c_0_70,negated_conjecture,
    ( v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_47])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_30]),c_0_46]),c_0_31]),c_0_47]),c_0_32]),c_0_24]),c_0_23])]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_73,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_65]),c_0_30]),c_0_46]),c_0_31]),c_0_47]),c_0_32]),c_0_24]),c_0_23])]),c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_66]),c_0_65]),c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_65]),c_0_66])).

cnf(c_0_76,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

fof(c_0_77,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_78,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_79,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k1_relset_1(X13,X14,X15),k1_zfmisc_1(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_74])).

cnf(c_0_81,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_83,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_84,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_85,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_86,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_27])).

cnf(c_0_87,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_84,c_0_55])).

fof(c_0_88,plain,(
    ! [X7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_89,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_82])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_23])).

cnf(c_0_91,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_24])])).

cnf(c_0_92,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_63]),c_0_47])])).

cnf(c_0_93,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_94,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | ~ m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(k1_relat_1(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_95,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_96,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_93])).

cnf(c_0_97,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_93])).

cnf(c_0_98,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_93])])).

cnf(c_0_99,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_25]),c_0_30]),c_0_46]),c_0_47]),c_0_26])])).

cnf(c_0_100,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = k1_xboole_0
    | esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_98]),c_0_50])).

fof(c_0_102,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | ~ v1_pre_topc(X22)
      | X22 = g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_103,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_38])).

cnf(c_0_104,plain,
    ( m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_27])).

cnf(c_0_105,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_106,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_100]),c_0_93])])).

cnf(c_0_107,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_101])).

cnf(c_0_108,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_110,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_45]),c_0_31]),c_0_32])])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_funct_2(X3,X1,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ),
    inference(spm,[status(thm)],[c_0_104,c_0_28])).

cnf(c_0_112,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | k1_xboole_0 != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_93])])).

cnf(c_0_113,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_27])).

cnf(c_0_114,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_45]),c_0_31]),c_0_32])])).

cnf(c_0_115,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),u1_pre_topc(g1_pre_topc(X1,X2))) = g1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_55])).

cnf(c_0_116,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_110,c_0_55])).

cnf(c_0_117,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_93]),c_0_93])]),c_0_112])).

cnf(c_0_118,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X4,X5,X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_114,c_0_55])).

cnf(c_0_120,negated_conjecture,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | esk3_0 = k1_xboole_0
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_101])).

cnf(c_0_121,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_96,c_0_83])).

cnf(c_0_122,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_63]),c_0_32])])).

cnf(c_0_123,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_92])).

cnf(c_0_124,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(esk3_0,u1_struct_0(esk1_0),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_92])).

cnf(c_0_125,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_72,c_0_117])).

cnf(c_0_126,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | X1 != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_117]),c_0_117])).

cnf(c_0_127,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X4,X5,X1) != X2
    | X2 != k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_117]),c_0_117])).

cnf(c_0_128,negated_conjecture,
    ( v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_25]),c_0_30]),c_0_46]),c_0_47]),c_0_26])])).

cnf(c_0_129,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_63]),c_0_32])])).

cnf(c_0_130,negated_conjecture,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))) = g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))
    | esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_63]),c_0_32])])).

cnf(c_0_131,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_105,c_0_121])).

cnf(c_0_132,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_92])).

cnf(c_0_133,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_123,c_0_95])).

cnf(c_0_134,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_124,c_0_95])).

cnf(c_0_135,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_63,c_0_101])).

cnf(c_0_136,plain,
    ( k1_relset_1(X1,X2,X3) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_relset_1(X1,X2,X3)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_89,c_0_83])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_92]),c_0_117])).

cnf(c_0_138,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_30]),c_0_46]),c_0_31]),c_0_47]),c_0_32]),c_0_24])])).

cnf(c_0_139,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_xboole_0 != X2
    | X1 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_121]),c_0_117])).

cnf(c_0_140,negated_conjecture,
    ( ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_128])).

cnf(c_0_141,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_142,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(X1,esk1_0,X2)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_101]),c_0_31]),c_0_32])]),c_0_131])).

cnf(c_0_143,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_101]),c_0_133]),c_0_134])).

cnf(c_0_144,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_95])).

cnf(c_0_145,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_135,c_0_55])).

cnf(c_0_146,plain,
    ( k1_relat_1(X1) = X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(X1))) ),
    inference(spm,[status(thm)],[c_0_136,c_0_27])).

cnf(c_0_147,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)))))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_101]),c_0_117])).

cnf(c_0_148,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_138,c_0_139])).

cnf(c_0_149,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_92]),c_0_141])).

cnf(c_0_150,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)
    | ~ v5_pre_topc(X1,esk1_0,X2)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2)))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_101]),c_0_31]),c_0_32])]),c_0_131])).

cnf(c_0_151,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142,c_0_143]),c_0_30]),c_0_46]),c_0_47]),c_0_24]),c_0_23])]),c_0_144])).

cnf(c_0_152,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145,c_0_63]),c_0_32])])).

cnf(c_0_153,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_140,c_0_117])).

cnf(c_0_154,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X1 != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_117]),c_0_117])).

cnf(c_0_155,negated_conjecture,
    ( k1_relat_1(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_93])])).

cnf(c_0_156,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_157,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_101]),c_0_133]),c_0_134])).

cnf(c_0_158,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_23]),c_0_30]),c_0_46]),c_0_47]),c_0_24])]),c_0_144]),c_0_151])).

cnf(c_0_159,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_130]),c_0_152])).

cnf(c_0_160,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_30]),c_0_46]),c_0_31]),c_0_47]),c_0_32]),c_0_24])])).

cnf(c_0_161,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | u1_struct_0(esk1_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_155])).

cnf(c_0_162,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_156,c_0_55])).

cnf(c_0_163,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),esk2_0)
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_157,c_0_95])).

cnf(c_0_164,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | v5_pre_topc(esk3_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_158,c_0_95])).

cnf(c_0_165,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_159,c_0_95])).

cnf(c_0_166,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_161]),c_0_95])).

cnf(c_0_167,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | esk3_0 != k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_63]),c_0_47])])).

cnf(c_0_168,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163,c_0_164]),c_0_165]),c_0_151])).

cnf(c_0_169,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 = k1_xboole_0
    | X1 != k1_xboole_0
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_170,plain,
    ( m1_subset_1(k1_relat_1(k1_relset_1(k2_zfmisc_1(X1,X2),X3,X4)),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_83])).

cnf(c_0_171,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | ~ v5_pre_topc(esk3_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_45]),c_0_31]),c_0_32])])).

cnf(c_0_172,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0
    | ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_167,c_0_168]),c_0_168])])).

cnf(c_0_173,plain,
    ( v1_funct_2(k1_relat_1(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4,X5)),X1,X2)
    | k1_relat_1(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4,X5)) != k1_xboole_0
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_170]),c_0_139])).

cnf(c_0_174,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_171,c_0_168]),c_0_168]),c_0_172])).

cnf(c_0_175,plain,
    ( v1_funct_2(k1_xboole_0,X1,X2)
    | X2 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173,c_0_106]),c_0_100]),c_0_100]),c_0_93])])).

cnf(c_0_176,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_174,c_0_175])).

cnf(c_0_177,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)
    | ~ m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_176,c_0_55])).

cnf(c_0_178,negated_conjecture,
    ( ~ v5_pre_topc(k1_xboole_0,esk1_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177,c_0_63]),c_0_32])])).

cnf(c_0_179,plain,
    ( v5_pre_topc(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_117]),c_0_117])).

cnf(c_0_180,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_168]),c_0_168]),c_0_168]),c_0_168]),c_0_93])]),c_0_178])).

cnf(c_0_181,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_30,c_0_168])).

cnf(c_0_182,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_24,c_0_168])).

cnf(c_0_183,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_180]),c_0_181]),c_0_46]),c_0_31]),c_0_47]),c_0_32]),c_0_182])]),c_0_178])).

cnf(c_0_184,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_183,c_0_139])).

cnf(c_0_185,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1))
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_42])).

cnf(c_0_186,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_161,c_0_184])).

cnf(c_0_187,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))) = k1_xboole_0
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_185,c_0_168]),c_0_93])])).

cnf(c_0_188,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_183,c_0_186])).

cnf(c_0_189,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))) = k1_xboole_0
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_187,c_0_186])).

cnf(c_0_190,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_188,c_0_175])).

cnf(c_0_191,negated_conjecture,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[c_0_189,c_0_190])).

cnf(c_0_192,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_96,c_0_191])).

cnf(c_0_193,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_131,c_0_93])).

cnf(c_0_194,plain,
    ( v5_pre_topc(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_117]),c_0_117])).

cnf(c_0_195,negated_conjecture,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122,c_0_168]),c_0_168]),c_0_168]),c_0_168]),c_0_93])]),c_0_192]),c_0_186]),c_0_193])]),c_0_178])).

cnf(c_0_196,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_182,c_0_186])).

cnf(c_0_197,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194,c_0_195]),c_0_181]),c_0_46]),c_0_31]),c_0_47]),c_0_32]),c_0_192]),c_0_186]),c_0_193]),c_0_186]),c_0_196])]),c_0_178]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:04:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.55/0.74  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.55/0.74  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.55/0.74  #
% 0.55/0.74  # Preprocessing time       : 0.043 s
% 0.55/0.74  
% 0.55/0.74  # Proof found!
% 0.55/0.74  # SZS status Theorem
% 0.55/0.74  # SZS output start CNFRefutation
% 0.55/0.74  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.55/0.74  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.55/0.74  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.55/0.74  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.55/0.74  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.55/0.74  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.55/0.74  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.55/0.74  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.55/0.74  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.55/0.74  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.55/0.74  fof(dt_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 0.55/0.74  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.55/0.74  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.55/0.74  fof(c_0_13, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.55/0.74  fof(c_0_14, negated_conjecture, ((v2_pre_topc(esk1_0)&l1_pre_topc(esk1_0))&((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))))&(esk3_0=esk4_0&((~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))&(v5_pre_topc(esk3_0,esk1_0,esk2_0)|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.55/0.74  fof(c_0_15, plain, ![X27, X28, X29, X30]:((~v5_pre_topc(X29,X27,X28)|v5_pre_topc(X30,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)),X28)|X29!=X30|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))&(~v5_pre_topc(X30,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)),X28)|v5_pre_topc(X29,X27,X28)|X29!=X30|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27))),u1_struct_0(X28)))))|(~v1_funct_1(X29)|~v1_funct_2(X29,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28)))))|(~v2_pre_topc(X28)|~l1_pre_topc(X28))|(~v2_pre_topc(X27)|~l1_pre_topc(X27)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.55/0.74  fof(c_0_16, plain, ![X19, X20, X21]:((((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X20=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&((~v1_funct_2(X21,X19,X20)|X19=k1_relset_1(X19,X20,X21)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X19!=k1_relset_1(X19,X20,X21)|v1_funct_2(X21,X19,X20)|X19!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))))&((~v1_funct_2(X21,X19,X20)|X21=k1_xboole_0|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(X21!=k1_xboole_0|v1_funct_2(X21,X19,X20)|X19=k1_xboole_0|X20!=k1_xboole_0|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.55/0.74  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_18, negated_conjecture, (esk3_0=esk4_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_19, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  fof(c_0_20, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.55/0.74  cnf(c_0_21, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.55/0.74  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.74  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_24, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.55/0.74  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(rw,[status(thm)],[c_0_19, c_0_18])).
% 0.55/0.74  cnf(c_0_27, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.55/0.74  cnf(c_0_28, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.74  cnf(c_0_29, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_21])).
% 0.55/0.74  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_31, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_32, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_33, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,esk2_0)|v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_34, negated_conjecture, (k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.55/0.74  cnf(c_0_35, negated_conjecture, (k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))),esk3_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_25]), c_0_26])])).
% 0.55/0.74  cnf(c_0_36, plain, (X1=k1_relat_1(X2)|X1!=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.55/0.74  cnf(c_0_37, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_25]), c_0_30]), c_0_31]), c_0_32]), c_0_26])])).
% 0.55/0.74  cnf(c_0_38, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_33, c_0_18])).
% 0.55/0.74  fof(c_0_39, plain, ![X26]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))|(~v2_pre_topc(X26)|~l1_pre_topc(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.55/0.74  cnf(c_0_40, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.74  cnf(c_0_41, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_34]), c_0_23])])).
% 0.55/0.74  cnf(c_0_42, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_35]), c_0_25])])).
% 0.55/0.74  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_25]), c_0_26])])).
% 0.55/0.74  cnf(c_0_44, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.55/0.74  cnf(c_0_45, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.55/0.74  cnf(c_0_46, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_47, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  fof(c_0_48, plain, ![X23, X24]:((v1_pre_topc(g1_pre_topc(X23,X24))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))))&(l1_pre_topc(g1_pre_topc(X23,X24))|~m1_subset_1(X24,k1_zfmisc_1(k1_zfmisc_1(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.55/0.74  fof(c_0_49, plain, ![X31, X32, X33, X34]:((~v5_pre_topc(X33,X31,X32)|v5_pre_topc(X34,X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))|X33!=X34|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32)))))|(~v2_pre_topc(X32)|~l1_pre_topc(X32))|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))&(~v5_pre_topc(X34,X31,g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))|v5_pre_topc(X33,X31,X32)|X33!=X34|(~v1_funct_1(X34)|~v1_funct_2(X34,u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32))))|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(g1_pre_topc(u1_struct_0(X32),u1_pre_topc(X32)))))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X31),u1_struct_0(X32))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X32)))))|(~v2_pre_topc(X32)|~l1_pre_topc(X32))|(~v2_pre_topc(X31)|~l1_pre_topc(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.55/0.74  cnf(c_0_50, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=k1_xboole_0|esk3_0=k1_xboole_0|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_25]), c_0_26])])).
% 0.55/0.74  cnf(c_0_51, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=u1_struct_0(esk1_0)|u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.55/0.74  cnf(c_0_52, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_43])).
% 0.55/0.74  cnf(c_0_53, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.55/0.74  cnf(c_0_54, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.55/0.74  cnf(c_0_55, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.55/0.74  fof(c_0_56, plain, ![X25]:(~l1_pre_topc(X25)|m1_subset_1(u1_pre_topc(X25),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X25))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.55/0.74  cnf(c_0_57, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.55/0.74  cnf(c_0_58, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.55/0.74  cnf(c_0_59, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v5_pre_topc(esk4_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.55/0.74  cnf(c_0_60, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_53])).
% 0.55/0.74  cnf(c_0_61, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.55/0.74  cnf(c_0_62, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.55/0.74  cnf(c_0_63, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.55/0.74  cnf(c_0_64, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_57])).
% 0.55/0.74  cnf(c_0_65, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(spm,[status(thm)],[c_0_25, c_0_58])).
% 0.55/0.74  cnf(c_0_66, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(spm,[status(thm)],[c_0_26, c_0_58])).
% 0.55/0.74  cnf(c_0_67, negated_conjecture, (~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(rw,[status(thm)],[c_0_59, c_0_18])).
% 0.55/0.74  cnf(c_0_68, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_25]), c_0_30]), c_0_31]), c_0_32]), c_0_26])])).
% 0.55/0.74  cnf(c_0_69, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_61])).
% 0.55/0.74  cnf(c_0_70, negated_conjecture, (v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_47])])).
% 0.55/0.74  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_30]), c_0_46]), c_0_31]), c_0_47]), c_0_32]), c_0_24]), c_0_23])]), c_0_66])).
% 0.55/0.74  cnf(c_0_72, negated_conjecture, (~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.55/0.74  cnf(c_0_73, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_65]), c_0_30]), c_0_46]), c_0_31]), c_0_47]), c_0_32]), c_0_24]), c_0_23])]), c_0_66])).
% 0.55/0.74  cnf(c_0_74, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_66]), c_0_65]), c_0_71])).
% 0.55/0.74  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_65]), c_0_66])).
% 0.55/0.74  cnf(c_0_76, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.55/0.74  fof(c_0_77, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.55/0.74  fof(c_0_78, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.55/0.74  fof(c_0_79, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|m1_subset_1(k1_relset_1(X13,X14,X15),k1_zfmisc_1(X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).
% 0.55/0.74  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_74])).
% 0.55/0.74  cnf(c_0_81, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.55/0.74  cnf(c_0_82, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.55/0.74  cnf(c_0_83, plain, (m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_79])).
% 0.55/0.74  cnf(c_0_84, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_45]), c_0_46]), c_0_47])])).
% 0.55/0.74  cnf(c_0_85, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.55/0.74  cnf(c_0_86, plain, (m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_83, c_0_27])).
% 0.55/0.74  cnf(c_0_87, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_84, c_0_55])).
% 0.55/0.74  fof(c_0_88, plain, ![X7]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.55/0.74  cnf(c_0_89, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_85, c_0_82])).
% 0.55/0.74  cnf(c_0_90, negated_conjecture, (m1_subset_1(k1_relat_1(esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_86, c_0_23])).
% 0.55/0.74  cnf(c_0_91, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|esk3_0=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_24])])).
% 0.55/0.74  cnf(c_0_92, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_63]), c_0_47])])).
% 0.55/0.74  cnf(c_0_93, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_88])).
% 0.55/0.74  cnf(c_0_94, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|~m1_subset_1(u1_struct_0(esk1_0),k1_zfmisc_1(k1_relat_1(esk3_0)))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.55/0.74  cnf(c_0_95, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.55/0.74  cnf(c_0_96, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_89, c_0_93])).
% 0.55/0.74  cnf(c_0_97, plain, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_86, c_0_93])).
% 0.55/0.74  cnf(c_0_98, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_93])])).
% 0.55/0.74  cnf(c_0_99, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_25]), c_0_30]), c_0_46]), c_0_47]), c_0_26])])).
% 0.55/0.74  cnf(c_0_100, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_97])).
% 0.55/0.74  cnf(c_0_101, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=k1_xboole_0|esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_98]), c_0_50])).
% 0.55/0.74  fof(c_0_102, plain, ![X22]:(~l1_pre_topc(X22)|(~v1_pre_topc(X22)|X22=g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.55/0.74  cnf(c_0_103, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_99, c_0_38])).
% 0.55/0.74  cnf(c_0_104, plain, (m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X4))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_86, c_0_27])).
% 0.55/0.74  cnf(c_0_105, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.74  cnf(c_0_106, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_100]), c_0_93])])).
% 0.55/0.74  cnf(c_0_107, negated_conjecture, (esk3_0=k1_xboole_0|v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_45, c_0_101])).
% 0.55/0.74  cnf(c_0_108, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.55/0.74  cnf(c_0_109, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.55/0.74  cnf(c_0_110, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_45]), c_0_31]), c_0_32])])).
% 0.55/0.74  cnf(c_0_111, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|X1!=k1_xboole_0|~v1_funct_2(X3,X1,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), inference(spm,[status(thm)],[c_0_104, c_0_28])).
% 0.55/0.74  cnf(c_0_112, plain, (v1_funct_2(k1_xboole_0,X1,X2)|k1_xboole_0!=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_93])])).
% 0.55/0.74  cnf(c_0_113, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_27, c_0_27])).
% 0.55/0.74  cnf(c_0_114, negated_conjecture, (esk3_0=k1_xboole_0|v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_45]), c_0_31]), c_0_32])])).
% 0.55/0.74  cnf(c_0_115, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),u1_pre_topc(g1_pre_topc(X1,X2)))=g1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_55])).
% 0.55/0.74  cnf(c_0_116, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_110, c_0_55])).
% 0.55/0.74  cnf(c_0_117, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_93]), c_0_93])]), c_0_112])).
% 0.55/0.74  cnf(c_0_118, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X4,X5,X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_105, c_0_113])).
% 0.55/0.74  cnf(c_0_119, negated_conjecture, (esk3_0=k1_xboole_0|v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_114, c_0_55])).
% 0.55/0.74  cnf(c_0_120, negated_conjecture, (g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))=g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))|esk3_0=k1_xboole_0|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_115, c_0_101])).
% 0.55/0.74  cnf(c_0_121, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_96, c_0_83])).
% 0.55/0.74  cnf(c_0_122, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_63]), c_0_32])])).
% 0.55/0.74  cnf(c_0_123, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),k1_xboole_0)))), inference(spm,[status(thm)],[c_0_23, c_0_92])).
% 0.55/0.74  cnf(c_0_124, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(esk3_0,u1_struct_0(esk1_0),k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_92])).
% 0.55/0.74  cnf(c_0_125, negated_conjecture, (esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(spm,[status(thm)],[c_0_72, c_0_117])).
% 0.55/0.74  cnf(c_0_126, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X1!=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_117]), c_0_117])).
% 0.55/0.74  cnf(c_0_127, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X4,X5,X1)!=X2|X2!=k1_xboole_0|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_117]), c_0_117])).
% 0.55/0.74  cnf(c_0_128, negated_conjecture, (v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_25]), c_0_30]), c_0_46]), c_0_47]), c_0_26])])).
% 0.55/0.74  cnf(c_0_129, negated_conjecture, (esk3_0=k1_xboole_0|v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_63]), c_0_32])])).
% 0.55/0.74  cnf(c_0_130, negated_conjecture, (g1_pre_topc(k1_xboole_0,u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))))=g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))|esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_63]), c_0_32])])).
% 0.55/0.74  cnf(c_0_131, plain, (v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_105, c_0_121])).
% 0.55/0.74  cnf(c_0_132, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)))), inference(spm,[status(thm)],[c_0_122, c_0_92])).
% 0.55/0.74  cnf(c_0_133, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_123, c_0_95])).
% 0.55/0.74  cnf(c_0_134, negated_conjecture, (esk3_0=k1_xboole_0|v1_funct_2(esk3_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_124, c_0_95])).
% 0.55/0.74  cnf(c_0_135, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_63, c_0_101])).
% 0.55/0.74  cnf(c_0_136, plain, (k1_relset_1(X1,X2,X3)=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_relset_1(X1,X2,X3)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_89, c_0_83])).
% 0.55/0.74  cnf(c_0_137, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_92]), c_0_117])).
% 0.55/0.74  cnf(c_0_138, negated_conjecture, (esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_30]), c_0_46]), c_0_31]), c_0_47]), c_0_32]), c_0_24])])).
% 0.55/0.74  cnf(c_0_139, plain, (v1_funct_2(X1,X2,X3)|k1_xboole_0!=X2|X1!=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_127, c_0_121]), c_0_117])).
% 0.55/0.74  cnf(c_0_140, negated_conjecture, (~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_67, c_0_128])).
% 0.55/0.74  cnf(c_0_141, negated_conjecture, (esk3_0=k1_xboole_0|v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_129, c_0_130])).
% 0.55/0.74  cnf(c_0_142, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(X1,esk1_0,X2)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_101]), c_0_31]), c_0_32])]), c_0_131])).
% 0.55/0.74  cnf(c_0_143, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_101]), c_0_133]), c_0_134])).
% 0.55/0.74  cnf(c_0_144, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_23, c_0_95])).
% 0.55/0.74  cnf(c_0_145, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_135, c_0_55])).
% 0.55/0.74  cnf(c_0_146, plain, (k1_relat_1(X1)=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X2,k1_zfmisc_1(k1_relat_1(X1)))), inference(spm,[status(thm)],[c_0_136, c_0_27])).
% 0.55/0.74  cnf(c_0_147, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))))))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_137, c_0_101]), c_0_117])).
% 0.55/0.74  cnf(c_0_148, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(spm,[status(thm)],[c_0_138, c_0_139])).
% 0.55/0.74  cnf(c_0_149, negated_conjecture, (esk3_0=k1_xboole_0|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140, c_0_92]), c_0_141])).
% 0.55/0.74  cnf(c_0_150, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(X1,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),X2)|~v5_pre_topc(X1,esk1_0,X2)|~v1_funct_1(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(esk1_0),u1_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(X2))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_101]), c_0_31]), c_0_32])]), c_0_131])).
% 0.55/0.74  cnf(c_0_151, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_142, c_0_143]), c_0_30]), c_0_46]), c_0_47]), c_0_24]), c_0_23])]), c_0_144])).
% 0.55/0.74  cnf(c_0_152, negated_conjecture, (esk3_0=k1_xboole_0|m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_145, c_0_63]), c_0_32])])).
% 0.55/0.74  cnf(c_0_153, negated_conjecture, (esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_140, c_0_117])).
% 0.55/0.74  cnf(c_0_154, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X1!=k1_xboole_0|~v5_pre_topc(X1,X2,X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_117]), c_0_117])).
% 0.55/0.74  cnf(c_0_155, negated_conjecture, (k1_relat_1(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146, c_0_147]), c_0_93])])).
% 0.55/0.74  cnf(c_0_156, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_148, c_0_45]), c_0_46]), c_0_47])])).
% 0.55/0.74  cnf(c_0_157, negated_conjecture, (esk3_0=k1_xboole_0|~v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_149, c_0_101]), c_0_133]), c_0_134])).
% 0.55/0.74  cnf(c_0_158, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150, c_0_23]), c_0_30]), c_0_46]), c_0_47]), c_0_24])]), c_0_144]), c_0_151])).
% 0.55/0.74  cnf(c_0_159, negated_conjecture, (esk3_0=k1_xboole_0|l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_130]), c_0_152])).
% 0.55/0.74  cnf(c_0_160, negated_conjecture, (esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_30]), c_0_46]), c_0_31]), c_0_47]), c_0_32]), c_0_24])])).
% 0.55/0.74  cnf(c_0_161, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|u1_struct_0(esk1_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_155])).
% 0.55/0.74  cnf(c_0_162, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_156, c_0_55])).
% 0.55/0.74  cnf(c_0_163, negated_conjecture, (esk3_0=k1_xboole_0|~v5_pre_topc(esk3_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),esk2_0)|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_157, c_0_95])).
% 0.55/0.74  cnf(c_0_164, negated_conjecture, (esk3_0=k1_xboole_0|v5_pre_topc(esk3_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)),esk2_0)), inference(spm,[status(thm)],[c_0_158, c_0_95])).
% 0.55/0.74  cnf(c_0_165, negated_conjecture, (esk3_0=k1_xboole_0|l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_159, c_0_95])).
% 0.55/0.74  cnf(c_0_166, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_160, c_0_161]), c_0_95])).
% 0.55/0.74  cnf(c_0_167, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|esk3_0!=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162, c_0_63]), c_0_47])])).
% 0.55/0.74  cnf(c_0_168, negated_conjecture, (esk3_0=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_163, c_0_164]), c_0_165]), c_0_151])).
% 0.55/0.74  cnf(c_0_169, plain, (v1_funct_2(X1,X2,X3)|X2=k1_xboole_0|X1!=k1_xboole_0|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.55/0.74  cnf(c_0_170, plain, (m1_subset_1(k1_relat_1(k1_relset_1(k2_zfmisc_1(X1,X2),X3,X4)),k1_zfmisc_1(X1))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)))), inference(spm,[status(thm)],[c_0_86, c_0_83])).
% 0.55/0.74  cnf(c_0_171, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|~v5_pre_topc(esk3_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(esk3_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_45]), c_0_31]), c_0_32])])).
% 0.55/0.74  cnf(c_0_172, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0|~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_167, c_0_168]), c_0_168])])).
% 0.55/0.74  cnf(c_0_173, plain, (v1_funct_2(k1_relat_1(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4,X5)),X1,X2)|k1_relat_1(k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4,X5))!=k1_xboole_0|X2!=k1_xboole_0|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_169, c_0_170]), c_0_139])).
% 0.55/0.74  cnf(c_0_174, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_xboole_0)), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_171, c_0_168]), c_0_168]), c_0_172])).
% 0.55/0.74  cnf(c_0_175, plain, (v1_funct_2(k1_xboole_0,X1,X2)|X2!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_173, c_0_106]), c_0_100]), c_0_100]), c_0_93])])).
% 0.55/0.74  cnf(c_0_176, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))), inference(spm,[status(thm)],[c_0_174, c_0_175])).
% 0.55/0.74  cnf(c_0_177, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)|~m1_subset_1(u1_pre_topc(esk1_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_176, c_0_55])).
% 0.55/0.74  cnf(c_0_178, negated_conjecture, (~v5_pre_topc(k1_xboole_0,esk1_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_177, c_0_63]), c_0_32])])).
% 0.55/0.74  cnf(c_0_179, plain, (v5_pre_topc(X1,X2,X3)|X1!=k1_xboole_0|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_117]), c_0_117])).
% 0.55/0.74  cnf(c_0_180, negated_conjecture, (v5_pre_topc(k1_xboole_0,esk1_0,g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))|~v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_168]), c_0_168]), c_0_168]), c_0_168]), c_0_93])]), c_0_178])).
% 0.55/0.74  cnf(c_0_181, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_30, c_0_168])).
% 0.55/0.74  cnf(c_0_182, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(rw,[status(thm)],[c_0_24, c_0_168])).
% 0.55/0.74  cnf(c_0_183, negated_conjecture, (~v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_179, c_0_180]), c_0_181]), c_0_46]), c_0_31]), c_0_47]), c_0_32]), c_0_182])]), c_0_178])).
% 0.55/0.74  cnf(c_0_184, negated_conjecture, (u1_struct_0(esk1_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_183, c_0_139])).
% 0.55/0.74  cnf(c_0_185, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0|m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1))|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_86, c_0_42])).
% 0.55/0.74  cnf(c_0_186, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_161, c_0_184])).
% 0.55/0.74  cnf(c_0_187, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk2_0),u1_pre_topc(esk2_0)))=k1_xboole_0|m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_185, c_0_168]), c_0_93])])).
% 0.55/0.74  cnf(c_0_188, negated_conjecture, (~v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0))))), inference(rw,[status(thm)],[c_0_183, c_0_186])).
% 0.55/0.74  cnf(c_0_189, negated_conjecture, (u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)))=k1_xboole_0|m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_187, c_0_186])).
% 0.55/0.74  cnf(c_0_190, negated_conjecture, (u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(esk2_0)))!=k1_xboole_0), inference(spm,[status(thm)],[c_0_188, c_0_175])).
% 0.55/0.74  cnf(c_0_191, negated_conjecture, (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0))),k1_zfmisc_1(X1))), inference(sr,[status(thm)],[c_0_189, c_0_190])).
% 0.55/0.74  cnf(c_0_192, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_96, c_0_191])).
% 0.55/0.74  cnf(c_0_193, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_131, c_0_93])).
% 0.55/0.74  cnf(c_0_194, plain, (v5_pre_topc(X1,X2,X3)|X1!=k1_xboole_0|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_117]), c_0_117])).
% 0.55/0.74  cnf(c_0_195, negated_conjecture, (v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(esk1_0),u1_pre_topc(esk1_0)),esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_122, c_0_168]), c_0_168]), c_0_168]), c_0_168]), c_0_93])]), c_0_192]), c_0_186]), c_0_193])]), c_0_178])).
% 0.55/0.74  cnf(c_0_196, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk1_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_182, c_0_186])).
% 0.55/0.74  cnf(c_0_197, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_194, c_0_195]), c_0_181]), c_0_46]), c_0_31]), c_0_47]), c_0_32]), c_0_192]), c_0_186]), c_0_193]), c_0_186]), c_0_196])]), c_0_178]), ['proof']).
% 0.55/0.74  # SZS output end CNFRefutation
% 0.55/0.74  # Proof object total steps             : 198
% 0.55/0.74  # Proof object clause steps            : 171
% 0.55/0.74  # Proof object formula steps           : 27
% 0.55/0.74  # Proof object conjectures             : 122
% 0.55/0.74  # Proof object clause conjectures      : 119
% 0.55/0.74  # Proof object formula conjectures     : 3
% 0.55/0.74  # Proof object initial clauses used    : 31
% 0.55/0.74  # Proof object initial formulas used   : 13
% 0.55/0.74  # Proof object generating inferences   : 120
% 0.55/0.74  # Proof object simplifying inferences  : 224
% 0.55/0.74  # Training examples: 0 positive, 0 negative
% 0.55/0.74  # Parsed axioms                        : 14
% 0.55/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.55/0.74  # Initial clauses                      : 38
% 0.55/0.74  # Removed in clause preprocessing      : 0
% 0.55/0.74  # Initial clauses in saturation        : 38
% 0.55/0.74  # Processed clauses                    : 1697
% 0.55/0.74  # ...of these trivial                  : 35
% 0.55/0.74  # ...subsumed                          : 824
% 0.55/0.74  # ...remaining for further processing  : 838
% 0.55/0.74  # Other redundant clauses eliminated   : 17
% 0.55/0.74  # Clauses deleted for lack of memory   : 0
% 0.55/0.74  # Backward-subsumed                    : 170
% 0.55/0.74  # Backward-rewritten                   : 372
% 0.55/0.74  # Generated clauses                    : 8858
% 0.55/0.74  # ...of the previous two non-trivial   : 7940
% 0.55/0.74  # Contextual simplify-reflections      : 146
% 0.55/0.74  # Paramodulations                      : 8774
% 0.55/0.74  # Factorizations                       : 53
% 0.55/0.74  # Equation resolutions                 : 25
% 0.55/0.74  # Propositional unsat checks           : 0
% 0.55/0.74  #    Propositional check models        : 0
% 0.55/0.74  #    Propositional check unsatisfiable : 0
% 0.55/0.74  #    Propositional clauses             : 0
% 0.55/0.74  #    Propositional clauses after purity: 0
% 0.55/0.74  #    Propositional unsat core size     : 0
% 0.55/0.74  #    Propositional preprocessing time  : 0.000
% 0.55/0.74  #    Propositional encoding time       : 0.000
% 0.55/0.74  #    Propositional solver time         : 0.000
% 0.55/0.74  #    Success case prop preproc time    : 0.000
% 0.55/0.74  #    Success case prop encoding time   : 0.000
% 0.55/0.74  #    Success case prop solver time     : 0.000
% 0.55/0.74  # Current number of processed clauses  : 284
% 0.55/0.74  #    Positive orientable unit clauses  : 27
% 0.55/0.74  #    Positive unorientable unit clauses: 0
% 0.55/0.74  #    Negative unit clauses             : 5
% 0.55/0.74  #    Non-unit-clauses                  : 252
% 0.55/0.74  # Current number of unprocessed clauses: 4894
% 0.55/0.74  # ...number of literals in the above   : 36667
% 0.55/0.74  # Current number of archived formulas  : 0
% 0.55/0.74  # Current number of archived clauses   : 548
% 0.55/0.74  # Clause-clause subsumption calls (NU) : 123267
% 0.55/0.74  # Rec. Clause-clause subsumption calls : 24376
% 0.55/0.74  # Non-unit clause-clause subsumptions  : 1113
% 0.55/0.74  # Unit Clause-clause subsumption calls : 1073
% 0.55/0.74  # Rewrite failures with RHS unbound    : 0
% 0.55/0.74  # BW rewrite match attempts            : 109
% 0.55/0.74  # BW rewrite match successes           : 12
% 0.55/0.74  # Condensation attempts                : 0
% 0.55/0.74  # Condensation successes               : 0
% 0.55/0.74  # Termbank termtop insertions          : 368274
% 0.55/0.74  
% 0.55/0.74  # -------------------------------------------------
% 0.55/0.74  # User time                : 0.397 s
% 0.55/0.74  # System time              : 0.016 s
% 0.55/0.74  # Total time               : 0.413 s
% 0.55/0.74  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
