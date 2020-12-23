%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 (1213 expanded)
%              Number of clauses        :   58 ( 424 expanded)
%              Number of leaves         :    7 ( 295 expanded)
%              Depth                    :   14
%              Number of atoms          :  280 (10734 expanded)
%              Number of equality atoms :   20 ( 716 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_pre_topc,conjecture,(
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

fof(d12_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( v4_pre_topc(X4,X2)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t61_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v4_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(c_0_7,negated_conjecture,(
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
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_pre_topc])).

fof(c_0_8,negated_conjecture,
    ( v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))
    & esk4_0 = esk5_0
    & ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | ~ v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) )
    & ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
      | v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_9,plain,(
    ! [X6,X7,X8,X9] :
      ( ( ~ v5_pre_topc(X8,X6,X7)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ v4_pre_topc(X9,X7)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8,X9),X6)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X7)))
        | v5_pre_topc(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( v4_pre_topc(esk1_3(X6,X7,X8),X7)
        | v5_pre_topc(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8,esk1_3(X6,X7,X8)),X6)
        | v5_pre_topc(X8,X6,X7)
        | ~ v1_funct_1(X8)
        | ~ v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7))))
        | ~ l1_pre_topc(X7)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(g1_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) )
      & ( l1_pre_topc(g1_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_14,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(X13)
      | m1_subset_1(u1_pre_topc(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_15,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))) ),
    inference(rw,[status(thm)],[c_0_12,c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_20,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_21,plain,(
    ! [X18,X19] :
      ( ( v4_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
        | ~ v4_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
        | ~ v4_pre_topc(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( v4_pre_topc(X19,X18)
        | ~ v4_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) )
      & ( m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ v4_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).

cnf(c_0_22,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_27,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_28,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_32,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_20,c_0_11])).

cnf(c_0_33,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_18]),c_0_25]),c_0_19])])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_36,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_23]),c_0_24]),c_0_18]),c_0_25]),c_0_19])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_38,plain,(
    ! [X14,X15,X16,X17] :
      ( ( X14 = X16
        | g1_pre_topc(X14,X15) != g1_pre_topc(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) )
      & ( X15 = X17
        | g1_pre_topc(X14,X15) != g1_pre_topc(X16,X17)
        | ~ m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

cnf(c_0_39,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,X1),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_25])]),c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_34]),c_0_35]),c_0_25])]),c_0_36])).

cnf(c_0_45,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_46,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( X1 = u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | g1_pre_topc(X1,X3) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_50,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_51,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_53,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)
    | v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_41]),c_0_25])])).

cnf(c_0_54,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_29])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_23]),c_0_24]),c_0_18]),c_0_25]),c_0_19])])).

cnf(c_0_56,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_41]),c_0_25])])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_41]),c_0_25])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_52,c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_25])]),c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ v5_pre_topc(esk4_0,esk2_0,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_23]),c_0_24]),c_0_18]),c_0_25]),c_0_19])])).

cnf(c_0_62,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0)
    | v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_35]),c_0_25])]),c_0_58])).

cnf(c_0_63,negated_conjecture,
    ( ~ v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60])])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_54]),c_0_25])])).

cnf(c_0_65,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_16]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_60])])).

cnf(c_0_67,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0) ),
    inference(sr,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[c_0_64,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_54]),c_0_25])])).

cnf(c_0_70,negated_conjecture,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_71,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_41]),c_0_25])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.20/0.40  # and selection function SelectCQIPrecWNTNp.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.028 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(t63_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.20/0.40  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.20/0.40  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.20/0.40  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.40  fof(t61_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v4_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v4_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_pre_topc)).
% 0.20/0.40  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.20/0.40  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.20/0.40  fof(c_0_7, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t63_pre_topc])).
% 0.20/0.40  fof(c_0_8, negated_conjecture, ((v2_pre_topc(esk2_0)&l1_pre_topc(esk2_0))&((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))&(esk4_0=esk5_0&((~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))&(v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.20/0.40  fof(c_0_9, plain, ![X6, X7, X8, X9]:((~v5_pre_topc(X8,X6,X7)|(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X7)))|(~v4_pre_topc(X9,X7)|v4_pre_topc(k8_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8,X9),X6)))|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6))&((m1_subset_1(esk1_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X7)))|v5_pre_topc(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6))&((v4_pre_topc(esk1_3(X6,X7,X8),X7)|v5_pre_topc(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X6),u1_struct_0(X7),X8,esk1_3(X6,X7,X8)),X6)|v5_pre_topc(X8,X6,X7)|(~v1_funct_1(X8)|~v1_funct_2(X8,u1_struct_0(X6),u1_struct_0(X7))|~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X6),u1_struct_0(X7)))))|~l1_pre_topc(X7)|~l1_pre_topc(X6))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.20/0.40  cnf(c_0_10, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_11, negated_conjecture, (esk4_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  fof(c_0_13, plain, ![X11, X12]:((v1_pre_topc(g1_pre_topc(X11,X12))|~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))))&(l1_pre_topc(g1_pre_topc(X11,X12))|~m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.20/0.40  fof(c_0_14, plain, ![X13]:(~l1_pre_topc(X13)|m1_subset_1(u1_pre_topc(X13),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X13))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.40  cnf(c_0_15, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_16, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.40  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))))))), inference(rw,[status(thm)],[c_0_12, c_0_11])).
% 0.20/0.40  cnf(c_0_18, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_20, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  fof(c_0_21, plain, ![X18, X19]:(((v4_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|(~v4_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))))|(~v4_pre_topc(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))&((v4_pre_topc(X19,X18)|(~v4_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18)))&(m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))|(~v4_pre_topc(X19,g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18)))|~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X18),u1_pre_topc(X18))))))|(~v2_pre_topc(X18)|~l1_pre_topc(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).
% 0.20/0.40  cnf(c_0_22, plain, (v4_pre_topc(esk1_3(X1,X2,X3),X2)|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_23, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_25, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_26, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  fof(c_0_27, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.20/0.40  cnf(c_0_28, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_29, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.40  cnf(c_0_30, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_31, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,X1),esk2_0)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_20, c_0_11])).
% 0.20/0.40  cnf(c_0_33, plain, (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),esk3_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_18]), c_0_25]), c_0_19])])).
% 0.20/0.40  cnf(c_0_35, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_23]), c_0_24]), c_0_18]), c_0_25]), c_0_19])])).
% 0.20/0.40  cnf(c_0_37, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v4_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  fof(c_0_38, plain, ![X14, X15, X16, X17]:((X14=X16|g1_pre_topc(X14,X15)!=g1_pre_topc(X16,X17)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))&(X15=X17|g1_pre_topc(X14,X15)!=g1_pre_topc(X16,X17)|~m1_subset_1(X15,k1_zfmisc_1(k1_zfmisc_1(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.20/0.40  cnf(c_0_39, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.40  cnf(c_0_40, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.40  cnf(c_0_41, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.40  cnf(c_0_42, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,X1),esk2_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.40  cnf(c_0_43, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,esk3_0,esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_25])]), c_0_36])).
% 0.20/0.40  cnf(c_0_44, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|m1_subset_1(esk1_3(esk2_0,esk3_0,esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_34]), c_0_35]), c_0_25])]), c_0_36])).
% 0.20/0.40  cnf(c_0_45, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.40  cnf(c_0_46, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.40  cnf(c_0_47, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.20/0.40  cnf(c_0_48, plain, (X1=u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|g1_pre_topc(X1,X3)!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.40  cnf(c_0_49, plain, (v5_pre_topc(X3,X1,X2)|~v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_50, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_16]), c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_51, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_52, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v5_pre_topc(esk5_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_53, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)|v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_41]), c_0_25])])).
% 0.20/0.40  cnf(c_0_54, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]), c_0_29])).
% 0.20/0.40  cnf(c_0_55, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)|~v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,esk3_0,esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_23]), c_0_24]), c_0_18]), c_0_25]), c_0_19])])).
% 0.20/0.40  cnf(c_0_56, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_57, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_41]), c_0_25])])).
% 0.20/0.40  cnf(c_0_58, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_41]), c_0_25])])).
% 0.20/0.40  cnf(c_0_59, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(rw,[status(thm)],[c_0_52, c_0_11])).
% 0.20/0.40  cnf(c_0_60, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_25])]), c_0_55])).
% 0.20/0.40  cnf(c_0_61, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)|~v4_pre_topc(X1,esk3_0)|~v5_pre_topc(esk4_0,esk2_0,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_23]), c_0_24]), c_0_18]), c_0_25]), c_0_19])])).
% 0.20/0.40  cnf(c_0_62, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0)|v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_35]), c_0_25])]), c_0_58])).
% 0.20/0.40  cnf(c_0_63, negated_conjecture, (~v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60])])).
% 0.20/0.40  cnf(c_0_64, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_54]), c_0_25])])).
% 0.20/0.40  cnf(c_0_65, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0))),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_16]), c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.40  cnf(c_0_66, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,X1),esk2_0)|~v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_60])])).
% 0.20/0.40  cnf(c_0_67, negated_conjecture, (v4_pre_topc(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),esk3_0)), inference(sr,[status(thm)],[c_0_62, c_0_63])).
% 0.20/0.40  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[c_0_64, c_0_63])).
% 0.20/0.40  cnf(c_0_69, negated_conjecture, (v5_pre_topc(esk4_0,esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))|~v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_54]), c_0_25])])).
% 0.20/0.40  cnf(c_0_70, negated_conjecture, (v4_pre_topc(k8_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk1_3(esk2_0,g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)),esk4_0)),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.20/0.40  cnf(c_0_71, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk3_0),u1_pre_topc(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69, c_0_70])]), c_0_63])).
% 0.20/0.40  cnf(c_0_72, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_41]), c_0_25])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 73
% 0.20/0.40  # Proof object clause steps            : 58
% 0.20/0.40  # Proof object formula steps           : 15
% 0.20/0.40  # Proof object conjectures             : 44
% 0.20/0.40  # Proof object clause conjectures      : 41
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 23
% 0.20/0.40  # Proof object initial formulas used   : 7
% 0.20/0.40  # Proof object generating inferences   : 26
% 0.20/0.40  # Proof object simplifying inferences  : 81
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 7
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 27
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 27
% 0.20/0.40  # Processed clauses                    : 241
% 0.20/0.40  # ...of these trivial                  : 3
% 0.20/0.40  # ...subsumed                          : 93
% 0.20/0.40  # ...remaining for further processing  : 145
% 0.20/0.40  # Other redundant clauses eliminated   : 0
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 14
% 0.20/0.40  # Backward-rewritten                   : 13
% 0.20/0.40  # Generated clauses                    : 684
% 0.20/0.40  # ...of the previous two non-trivial   : 665
% 0.20/0.40  # Contextual simplify-reflections      : 42
% 0.20/0.40  # Paramodulations                      : 666
% 0.20/0.40  # Factorizations                       : 0
% 0.20/0.40  # Equation resolutions                 : 14
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 88
% 0.20/0.40  #    Positive orientable unit clauses  : 16
% 0.20/0.40  #    Positive unorientable unit clauses: 0
% 0.20/0.40  #    Negative unit clauses             : 2
% 0.20/0.40  #    Non-unit-clauses                  : 70
% 0.20/0.40  # Current number of unprocessed clauses: 476
% 0.20/0.40  # ...number of literals in the above   : 1996
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 57
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 4062
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 1742
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 149
% 0.20/0.40  # Unit Clause-clause subsumption calls : 67
% 0.20/0.40  # Rewrite failures with RHS unbound    : 0
% 0.20/0.40  # BW rewrite match attempts            : 14
% 0.20/0.40  # BW rewrite match successes           : 2
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 23664
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.054 s
% 0.20/0.40  # System time              : 0.003 s
% 0.20/0.40  # Total time               : 0.056 s
% 0.20/0.40  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
