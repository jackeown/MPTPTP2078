%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:12 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   41 (3942 expanded)
%              Number of clauses        :   34 (1103 expanded)
%              Number of leaves         :    3 ( 978 expanded)
%              Depth                    :   11
%              Number of atoms          :  326 (44406 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal clause size      :   60 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_tmap_1,conjecture,(
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
             => ( v5_pre_topc(X3,X2,X1)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(d3_borsuk_1,axiom,(
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
             => ( v5_pre_topc(X3,X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
                       => ? [X6] :
                            ( m1_connsp_2(X6,X1,X4)
                            & r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X6),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_borsuk_1)).

fof(d2_tmap_1,axiom,(
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
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_tmap_1(X1,X2,X3,X4)
                  <=> ! [X5] :
                        ( m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
                       => ? [X6] :
                            ( m1_connsp_2(X6,X1,X4)
                            & r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X6),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tmap_1)).

fof(c_0_3,negated_conjecture,(
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
               => ( v5_pre_topc(X3,X2,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X2))
                     => r1_tmap_1(X2,X1,X3,X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_tmap_1])).

fof(c_0_4,plain,(
    ! [X15,X16,X17,X18,X19,X23] :
      ( ( m1_connsp_2(esk3_5(X15,X16,X17,X18,X19),X15,X18)
        | ~ m1_connsp_2(X19,X16,k3_funct_2(u1_struct_0(X15),u1_struct_0(X16),X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( r1_tarski(k7_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk3_5(X15,X16,X17,X18,X19)),X19)
        | ~ m1_connsp_2(X19,X16,k3_funct_2(u1_struct_0(X15),u1_struct_0(X16),X17,X18))
        | ~ m1_subset_1(X18,u1_struct_0(X15))
        | ~ v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_subset_1(esk4_3(X15,X16,X17),u1_struct_0(X15))
        | v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( m1_connsp_2(esk5_3(X15,X16,X17),X16,k3_funct_2(u1_struct_0(X15),u1_struct_0(X16),X17,esk4_3(X15,X16,X17)))
        | v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ m1_connsp_2(X23,X15,esk4_3(X15,X16,X17))
        | ~ r1_tarski(k7_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X23),esk5_3(X15,X16,X17))
        | v5_pre_topc(X17,X15,X16)
        | ~ v1_funct_1(X17)
        | ~ v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16))))
        | v2_struct_0(X16)
        | ~ v2_pre_topc(X16)
        | ~ l1_pre_topc(X16)
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_borsuk_1])])])])])])).

fof(c_0_5,negated_conjecture,(
    ! [X28] :
      ( ~ v2_struct_0(esk6_0)
      & v2_pre_topc(esk6_0)
      & l1_pre_topc(esk6_0)
      & ~ v2_struct_0(esk7_0)
      & v2_pre_topc(esk7_0)
      & l1_pre_topc(esk7_0)
      & v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk6_0))
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0))))
      & ( m1_subset_1(esk9_0,u1_struct_0(esk7_0))
        | ~ v5_pre_topc(esk8_0,esk7_0,esk6_0) )
      & ( ~ r1_tmap_1(esk7_0,esk6_0,esk8_0,esk9_0)
        | ~ v5_pre_topc(esk8_0,esk7_0,esk6_0) )
      & ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
        | ~ m1_subset_1(X28,u1_struct_0(esk7_0))
        | r1_tmap_1(esk7_0,esk6_0,esk8_0,X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).

cnf(c_0_6,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))
    | v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_7,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_8,negated_conjecture,
    ( v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_16,plain,(
    ! [X7,X8,X9,X10,X11,X14] :
      ( ( m1_connsp_2(esk1_5(X7,X8,X9,X10,X11),X7,X10)
        | ~ m1_connsp_2(X11,X8,k3_funct_2(u1_struct_0(X7),u1_struct_0(X8),X9,X10))
        | ~ r1_tmap_1(X7,X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( r1_tarski(k7_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,esk1_5(X7,X8,X9,X10,X11)),X11)
        | ~ m1_connsp_2(X11,X8,k3_funct_2(u1_struct_0(X7),u1_struct_0(X8),X9,X10))
        | ~ r1_tmap_1(X7,X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( m1_connsp_2(esk2_4(X7,X8,X9,X10),X8,k3_funct_2(u1_struct_0(X7),u1_struct_0(X8),X9,X10))
        | r1_tmap_1(X7,X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_connsp_2(X14,X7,X10)
        | ~ r1_tarski(k7_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,X14),esk2_4(X7,X8,X9,X10))
        | r1_tmap_1(X7,X8,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(X7))
        | ~ v1_funct_1(X9)
        | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
        | v2_struct_0(X8)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8)
        | v2_struct_0(X7)
        | ~ v2_pre_topc(X7)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tmap_1])])])])])])).

cnf(c_0_17,plain,
    ( m1_connsp_2(esk5_3(X1,X2,X3),X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3)))
    | v5_pre_topc(X3,X1,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_18,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
    | r1_tmap_1(esk7_0,esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_19,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
    | m1_subset_1(esk4_3(esk7_0,esk6_0,esk8_0),u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_20,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X1,X2,X3,X4,X5)),X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
    | m1_connsp_2(esk5_3(esk7_0,esk6_0,esk8_0),esk6_0,k3_funct_2(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk4_3(esk7_0,esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
    | r1_tmap_1(esk7_0,esk6_0,esk8_0,esk4_3(esk7_0,esk6_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( m1_connsp_2(esk1_5(X1,X2,X3,X4,X5),X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( v5_pre_topc(X4,X2,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,esk4_3(X2,X3,X4))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X4,X1),esk5_3(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_25,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
    | r1_tarski(k7_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk1_5(esk7_0,esk6_0,esk8_0,esk4_3(esk7_0,esk6_0,esk8_0),esk5_3(esk7_0,esk6_0,esk8_0))),esk5_3(esk7_0,esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15]),c_0_19]),c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0)
    | m1_connsp_2(esk1_5(esk7_0,esk6_0,esk8_0,esk4_3(esk7_0,esk6_0,esk8_0),esk5_3(esk7_0,esk6_0,esk8_0)),esk7_0,esk4_3(esk7_0,esk6_0,esk8_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_21]),c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15]),c_0_19]),c_0_22])).

cnf(c_0_27,plain,
    ( m1_connsp_2(esk2_4(X1,X2,X3,X4),X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0))
    | ~ v5_pre_topc(esk8_0,esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_29,negated_conjecture,
    ( v5_pre_topc(esk8_0,esk7_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15]),c_0_26])).

cnf(c_0_30,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk6_0,esk8_0,esk9_0)
    | ~ v5_pre_topc(esk8_0,esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_31,negated_conjecture,
    ( m1_connsp_2(esk2_4(esk7_0,esk6_0,esk8_0,X1),esk6_0,k3_funct_2(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,X1))
    | r1_tmap_1(esk7_0,esk6_0,esk8_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_7]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,esk6_0,esk8_0,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_29])])).

cnf(c_0_34,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_5(X1,X2,X3,X4,X5)),X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_35,negated_conjecture,
    ( m1_connsp_2(esk2_4(esk7_0,esk6_0,esk8_0,esk9_0),esk6_0,k3_funct_2(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_36,plain,
    ( m1_connsp_2(esk3_5(X1,X2,X3,X4,X5),X1,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_4])).

cnf(c_0_37,plain,
    ( r1_tmap_1(X2,X4,X5,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X4),X5,X1),esk2_4(X2,X4,X5,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk3_5(esk7_0,esk6_0,esk8_0,esk9_0,esk2_4(esk7_0,esk6_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk6_0,esk8_0,esk9_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_29]),c_0_7]),c_0_32]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( m1_connsp_2(esk3_5(esk7_0,esk6_0,esk8_0,esk9_0,esk2_4(esk7_0,esk6_0,esk8_0,esk9_0)),esk7_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_35]),c_0_29]),c_0_7]),c_0_32]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14]),c_0_15])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_7]),c_0_32]),c_0_8]),c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_33]),c_0_14]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  # Presaturation interreduction done
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t49_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tmap_1)).
% 0.12/0.37  fof(d3_borsuk_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>![X5]:(m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))=>?[X6]:(m1_connsp_2(X6,X1,X4)&r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X6),X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_borsuk_1)).
% 0.12/0.37  fof(d2_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r1_tmap_1(X1,X2,X3,X4)<=>![X5]:(m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))=>?[X6]:(m1_connsp_2(X6,X1,X4)&r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X6),X5)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tmap_1)).
% 0.12/0.37  fof(c_0_3, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>(v5_pre_topc(X3,X2,X1)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>r1_tmap_1(X2,X1,X3,X4))))))), inference(assume_negation,[status(cth)],[t49_tmap_1])).
% 0.12/0.37  fof(c_0_4, plain, ![X15, X16, X17, X18, X19, X23]:(((m1_connsp_2(esk3_5(X15,X16,X17,X18,X19),X15,X18)|~m1_connsp_2(X19,X16,k3_funct_2(u1_struct_0(X15),u1_struct_0(X16),X17,X18))|~m1_subset_1(X18,u1_struct_0(X15))|~v5_pre_topc(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(r1_tarski(k7_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,esk3_5(X15,X16,X17,X18,X19)),X19)|~m1_connsp_2(X19,X16,k3_funct_2(u1_struct_0(X15),u1_struct_0(X16),X17,X18))|~m1_subset_1(X18,u1_struct_0(X15))|~v5_pre_topc(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15))))&((m1_subset_1(esk4_3(X15,X16,X17),u1_struct_0(X15))|v5_pre_topc(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&((m1_connsp_2(esk5_3(X15,X16,X17),X16,k3_funct_2(u1_struct_0(X15),u1_struct_0(X16),X17,esk4_3(X15,X16,X17)))|v5_pre_topc(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))&(~m1_connsp_2(X23,X15,esk4_3(X15,X16,X17))|~r1_tarski(k7_relset_1(u1_struct_0(X15),u1_struct_0(X16),X17,X23),esk5_3(X15,X16,X17))|v5_pre_topc(X17,X15,X16)|(~v1_funct_1(X17)|~v1_funct_2(X17,u1_struct_0(X15),u1_struct_0(X16))|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),u1_struct_0(X16)))))|(v2_struct_0(X16)|~v2_pre_topc(X16)|~l1_pre_topc(X16))|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d3_borsuk_1])])])])])])).
% 0.12/0.37  fof(c_0_5, negated_conjecture, ![X28]:(((~v2_struct_0(esk6_0)&v2_pre_topc(esk6_0))&l1_pre_topc(esk6_0))&(((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk6_0)))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0)))))&(((m1_subset_1(esk9_0,u1_struct_0(esk7_0))|~v5_pre_topc(esk8_0,esk7_0,esk6_0))&(~r1_tmap_1(esk7_0,esk6_0,esk8_0,esk9_0)|~v5_pre_topc(esk8_0,esk7_0,esk6_0)))&(v5_pre_topc(esk8_0,esk7_0,esk6_0)|(~m1_subset_1(X28,u1_struct_0(esk7_0))|r1_tmap_1(esk7_0,esk6_0,esk8_0,X28))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_3])])])])])])).
% 0.12/0.37  cnf(c_0_6, plain, (m1_subset_1(esk4_3(X1,X2,X3),u1_struct_0(X1))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_7, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0))))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_8, negated_conjecture, (v1_funct_2(esk8_0,u1_struct_0(esk7_0),u1_struct_0(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_9, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_10, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_12, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_13, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  fof(c_0_16, plain, ![X7, X8, X9, X10, X11, X14]:(((m1_connsp_2(esk1_5(X7,X8,X9,X10,X11),X7,X10)|~m1_connsp_2(X11,X8,k3_funct_2(u1_struct_0(X7),u1_struct_0(X8),X9,X10))|~r1_tmap_1(X7,X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X7))|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(r1_tarski(k7_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,esk1_5(X7,X8,X9,X10,X11)),X11)|~m1_connsp_2(X11,X8,k3_funct_2(u1_struct_0(X7),u1_struct_0(X8),X9,X10))|~r1_tmap_1(X7,X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X7))|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7))))&((m1_connsp_2(esk2_4(X7,X8,X9,X10),X8,k3_funct_2(u1_struct_0(X7),u1_struct_0(X8),X9,X10))|r1_tmap_1(X7,X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X7))|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7)))&(~m1_connsp_2(X14,X7,X10)|~r1_tarski(k7_relset_1(u1_struct_0(X7),u1_struct_0(X8),X9,X14),esk2_4(X7,X8,X9,X10))|r1_tmap_1(X7,X8,X9,X10)|~m1_subset_1(X10,u1_struct_0(X7))|(~v1_funct_1(X9)|~v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8)))))|(v2_struct_0(X8)|~v2_pre_topc(X8)|~l1_pre_topc(X8))|(v2_struct_0(X7)|~v2_pre_topc(X7)|~l1_pre_topc(X7))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tmap_1])])])])])])).
% 0.12/0.37  cnf(c_0_17, plain, (m1_connsp_2(esk5_3(X1,X2,X3),X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk4_3(X1,X2,X3)))|v5_pre_topc(X3,X1,X2)|v2_struct_0(X2)|v2_struct_0(X1)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)|r1_tmap_1(esk7_0,esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)|m1_subset_1(esk4_3(esk7_0,esk6_0,esk8_0),u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_20, plain, (r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X1,X2,X3,X4,X5)),X5)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))|~r1_tmap_1(X1,X2,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)|m1_connsp_2(esk5_3(esk7_0,esk6_0,esk8_0),esk6_0,k3_funct_2(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk4_3(esk7_0,esk6_0,esk8_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)|r1_tmap_1(esk7_0,esk6_0,esk8_0,esk4_3(esk7_0,esk6_0,esk8_0))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.37  cnf(c_0_23, plain, (m1_connsp_2(esk1_5(X1,X2,X3,X4,X5),X1,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))|~r1_tmap_1(X1,X2,X3,X4)|~m1_subset_1(X4,u1_struct_0(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_24, plain, (v5_pre_topc(X4,X2,X3)|v2_struct_0(X3)|v2_struct_0(X2)|~m1_connsp_2(X1,X2,esk4_3(X2,X3,X4))|~r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X3),X4,X1),esk5_3(X2,X3,X4))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)|r1_tarski(k7_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk1_5(esk7_0,esk6_0,esk8_0,esk4_3(esk7_0,esk6_0,esk8_0),esk5_3(esk7_0,esk6_0,esk8_0))),esk5_3(esk7_0,esk6_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15]), c_0_19]), c_0_22])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)|m1_connsp_2(esk1_5(esk7_0,esk6_0,esk8_0,esk4_3(esk7_0,esk6_0,esk8_0),esk5_3(esk7_0,esk6_0,esk8_0)),esk7_0,esk4_3(esk7_0,esk6_0,esk8_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_21]), c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15]), c_0_19]), c_0_22])).
% 0.12/0.37  cnf(c_0_27, plain, (m1_connsp_2(esk2_4(X1,X2,X3,X4),X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))|r1_tmap_1(X1,X2,X3,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X1))|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))|~v5_pre_topc(esk8_0,esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_29, negated_conjecture, (v5_pre_topc(esk8_0,esk7_0,esk6_0)), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15]), c_0_26])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (~r1_tmap_1(esk7_0,esk6_0,esk8_0,esk9_0)|~v5_pre_topc(esk8_0,esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.12/0.37  cnf(c_0_31, negated_conjecture, (m1_connsp_2(esk2_4(esk7_0,esk6_0,esk8_0,X1),esk6_0,k3_funct_2(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,X1))|r1_tmap_1(esk7_0,esk6_0,esk8_0,X1)|~m1_subset_1(X1,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_7]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk9_0,u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29])])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (~r1_tmap_1(esk7_0,esk6_0,esk8_0,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_29])])).
% 0.12/0.37  cnf(c_0_34, plain, (r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk3_5(X1,X2,X3,X4,X5)),X5)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_35, negated_conjecture, (m1_connsp_2(esk2_4(esk7_0,esk6_0,esk8_0,esk9_0),esk6_0,k3_funct_2(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.12/0.37  cnf(c_0_36, plain, (m1_connsp_2(esk3_5(X1,X2,X3,X4,X5),X1,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_connsp_2(X5,X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4))|~m1_subset_1(X4,u1_struct_0(X1))|~v5_pre_topc(X3,X1,X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_4])).
% 0.12/0.37  cnf(c_0_37, plain, (r1_tmap_1(X2,X4,X5,X3)|v2_struct_0(X4)|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X4),X5,X1),esk2_4(X2,X4,X5,X3))|~m1_subset_1(X3,u1_struct_0(X2))|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))|~v2_pre_topc(X4)|~l1_pre_topc(X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk7_0),u1_struct_0(esk6_0),esk8_0,esk3_5(esk7_0,esk6_0,esk8_0,esk9_0,esk2_4(esk7_0,esk6_0,esk8_0,esk9_0))),esk2_4(esk7_0,esk6_0,esk8_0,esk9_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_29]), c_0_7]), c_0_32]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_39, negated_conjecture, (m1_connsp_2(esk3_5(esk7_0,esk6_0,esk8_0,esk9_0,esk2_4(esk7_0,esk6_0,esk8_0,esk9_0)),esk7_0,esk9_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_35]), c_0_29]), c_0_7]), c_0_32]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14]), c_0_15])).
% 0.12/0.37  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_39]), c_0_7]), c_0_32]), c_0_8]), c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_33]), c_0_14]), c_0_15]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 41
% 0.12/0.37  # Proof object clause steps            : 34
% 0.12/0.37  # Proof object formula steps           : 7
% 0.12/0.37  # Proof object conjectures             : 28
% 0.12/0.37  # Proof object clause conjectures      : 25
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 21
% 0.12/0.37  # Proof object initial formulas used   : 3
% 0.12/0.37  # Proof object generating inferences   : 11
% 0.12/0.37  # Proof object simplifying inferences  : 104
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 3
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 21
% 0.12/0.37  # Removed in clause preprocessing      : 0
% 0.12/0.37  # Initial clauses in saturation        : 21
% 0.12/0.37  # Processed clauses                    : 56
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 2
% 0.12/0.37  # ...remaining for further processing  : 54
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 0
% 0.12/0.37  # Backward-rewritten                   : 8
% 0.12/0.37  # Generated clauses                    : 16
% 0.12/0.37  # ...of the previous two non-trivial   : 15
% 0.12/0.37  # Contextual simplify-reflections      : 5
% 0.12/0.37  # Paramodulations                      : 16
% 0.12/0.37  # Factorizations                       : 0
% 0.12/0.37  # Equation resolutions                 : 0
% 0.12/0.37  # Propositional unsat checks           : 0
% 0.12/0.37  #    Propositional check models        : 0
% 0.12/0.37  #    Propositional check unsatisfiable : 0
% 0.12/0.37  #    Propositional clauses             : 0
% 0.12/0.37  #    Propositional clauses after purity: 0
% 0.12/0.37  #    Propositional unsat core size     : 0
% 0.12/0.37  #    Propositional preprocessing time  : 0.000
% 0.12/0.37  #    Propositional encoding time       : 0.000
% 0.12/0.37  #    Propositional solver time         : 0.000
% 0.12/0.37  #    Success case prop preproc time    : 0.000
% 0.12/0.37  #    Success case prop encoding time   : 0.000
% 0.12/0.37  #    Success case prop solver time     : 0.000
% 0.12/0.37  # Current number of processed clauses  : 25
% 0.12/0.37  #    Positive orientable unit clauses  : 12
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 3
% 0.12/0.37  #    Non-unit-clauses                  : 10
% 0.12/0.37  # Current number of unprocessed clauses: 1
% 0.12/0.37  # ...number of literals in the above   : 2
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 29
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 167
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 28
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 6
% 0.12/0.37  # Unit Clause-clause subsumption calls : 16
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 2
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 4421
% 0.12/0.37  
% 0.12/0.37  # -------------------------------------------------
% 0.12/0.37  # User time                : 0.035 s
% 0.12/0.37  # System time              : 0.002 s
% 0.12/0.37  # Total time               : 0.037 s
% 0.12/0.37  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
