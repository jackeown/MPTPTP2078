%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1132+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:47 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   68 (2022 expanded)
%              Number of clauses        :   55 ( 717 expanded)
%              Number of leaves         :    6 ( 479 expanded)
%              Depth                    :   20
%              Number of atoms          :  256 (17970 expanded)
%              Number of equality atoms :    9 (1179 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   30 (   2 average)
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

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

fof(c_0_6,negated_conjecture,(
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

fof(c_0_7,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))
    & esk6_0 = esk7_0
    & ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | ~ v5_pre_topc(esk7_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) )
    & ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | v5_pre_topc(esk7_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_8,plain,(
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

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v4_pre_topc(esk1_3(X1,X2,X3),X2)
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_17,plain,(
    ! [X11,X12] :
      ( ( v1_pre_topc(g1_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) )
      & ( l1_pre_topc(g1_pre_topc(X11,X12))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k1_zfmisc_1(X11))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_20,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | m1_subset_1(u1_pre_topc(X17),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X17)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_22,plain,(
    ! [X21,X22,X23,X24] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k8_relset_1(X21,X22,X23,X24) = k10_relat_1(X23,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_23,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | m1_subset_1(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

fof(c_0_24,plain,(
    ! [X33,X34] :
      ( ( v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))
        | ~ v4_pre_topc(X34,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( v4_pre_topc(X34,X33)
        | ~ v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ v4_pre_topc(X34,g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X33),u1_pre_topc(X33)))))
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t61_pre_topc])])])])).

cnf(c_0_25,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_26,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | m1_subset_1(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_31,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,plain,
    ( v5_pre_topc(X3,X1,X2)
    | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_3(X1,X2,X3)),X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_35,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),esk6_0,X1) = k10_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_13])).

cnf(c_0_36,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_37,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0),esk6_0,X1) = k10_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_40,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | m1_subset_1(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_26]),c_0_27])])).

cnf(c_0_41,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk7_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_42,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_27])])).

cnf(c_0_43,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_44,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v4_pre_topc(k10_relat_1(esk6_0,esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0)),esk4_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_13]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_45,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk6_0,X1),esk4_0)
    | ~ v4_pre_topc(X1,esk5_0)
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_29]),c_0_38]),c_0_15]),c_0_27]),c_0_16])])).

cnf(c_0_46,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | m1_subset_1(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_33]),c_0_27])]),c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_41,c_0_10])).

cnf(c_0_48,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)),esk6_0),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_43,c_0_10])).

cnf(c_0_50,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_51,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_52,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_26]),c_0_27])])).

cnf(c_0_54,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_47,c_0_53])).

cnf(c_0_55,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v4_pre_topc(k10_relat_1(esk6_0,esk1_3(esk4_0,esk5_0,esk6_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_37]),c_0_29]),c_0_38]),c_0_15]),c_0_27]),c_0_16])])).

cnf(c_0_56,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk6_0,X1),esk4_0)
    | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_54])])).

cnf(c_0_57,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,esk5_0,esk6_0),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_29]),c_0_38]),c_0_15]),c_0_27]),c_0_16])])).

cnf(c_0_58,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_29]),c_0_38]),c_0_15]),c_0_27]),c_0_16])])).

cnf(c_0_59,negated_conjecture,
    ( ~ v4_pre_topc(esk1_3(esk4_0,esk5_0,esk6_0),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_53])).

cnf(c_0_60,plain,
    ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_61,negated_conjecture,
    ( v4_pre_topc(esk1_3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(sr,[status(thm)],[c_0_57,c_0_53])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_58,c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( ~ m1_subset_1(esk1_3(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_33]),c_0_61]),c_0_62]),c_0_27])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v4_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_65,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_33]),c_0_61]),c_0_62]),c_0_27])])).

cnf(c_0_66,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_20])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_26]),c_0_27])]),
    [proof]).

%------------------------------------------------------------------------------
