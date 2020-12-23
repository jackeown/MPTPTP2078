%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1740+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:41 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
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
