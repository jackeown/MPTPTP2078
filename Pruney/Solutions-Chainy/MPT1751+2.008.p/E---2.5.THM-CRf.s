%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 185 expanded)
%              Number of clauses        :   47 (  68 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  240 (1396 expanded)
%              Number of equality atoms :   24 ( 114 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   21 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t61_tmap_1,conjecture,(
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
                      ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( r1_tarski(X5,u1_struct_0(X3))
                       => k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

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

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(t178_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ~ v1_xboole_0(X4)
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_funct_2(X5,X1,X4)
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) )
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k7_relset_1(X1,X4,X5,X2),X3) )
           => ( v1_funct_1(k2_partfun1(X1,X4,X5,X2))
              & v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3)
              & m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

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

fof(c_0_12,plain,(
    ! [X6,X7] :
      ( ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
        | r1_tarski(X6,X7) )
      & ( ~ r1_tarski(X6,X7)
        | m1_subset_1(X6,k1_zfmisc_1(X7)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | m1_subset_1(k7_relset_1(X14,X15,X16,X17),k1_zfmisc_1(X15)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

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
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X2) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                   => ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                       => ( r1_tarski(X5,u1_struct_0(X3))
                         => k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5) = k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_tmap_1])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,plain,(
    ! [X18,X19,X20,X21] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | k7_relset_1(X18,X19,X20,X21) = k9_relat_1(X20,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_18,plain,(
    ! [X33,X34,X35,X36] :
      ( v2_struct_0(X33)
      | ~ v2_pre_topc(X33)
      | ~ l1_pre_topc(X33)
      | v2_struct_0(X34)
      | ~ v2_pre_topc(X34)
      | ~ l1_pre_topc(X34)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))
      | ~ m1_pre_topc(X36,X33)
      | k2_tmap_1(X33,X34,X35,X36) = k2_partfun1(u1_struct_0(X33),u1_struct_0(X34),X35,u1_struct_0(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & r1_tarski(esk5_0,u1_struct_0(esk3_0))
    & k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_20,plain,
    ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25]),c_0_26]),c_0_27]),c_0_28]),c_0_29])]),c_0_30]),c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_37,plain,(
    ! [X22,X23,X24,X25] :
      ( ~ v1_funct_1(X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k2_partfun1(X22,X23,X24,X25) = k7_relat_1(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_38,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_relat_1(X8)
      | ~ r1_tarski(X9,X10)
      | k9_relat_1(k7_relat_1(X8,X10),X9) = k9_relat_1(X8,X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

fof(c_0_39,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(k9_relat_1(X1,X2),X3)
    | ~ r1_tarski(X1,k2_zfmisc_1(X4,X3)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_42,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,plain,
    ( r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
    | ~ r1_tarski(X3,k2_zfmisc_1(X6,X5))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_21])).

fof(c_0_46,plain,(
    ! [X37,X38] :
      ( ~ l1_pre_topc(X37)
      | ~ m1_pre_topc(X38,X37)
      | m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_47,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_29]),c_0_23])])).

cnf(c_0_48,plain,
    ( k7_relset_1(X1,X2,k7_relat_1(X3,X4),X5) = k9_relat_1(X3,X5)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X5,X4)
    | ~ m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_23])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_51,plain,(
    ! [X26,X27,X28,X29,X30] :
      ( ( v1_funct_1(k2_partfun1(X26,X29,X30,X27))
        | ~ r1_tarski(X27,X26)
        | ~ r1_tarski(k7_relset_1(X26,X29,X30,X27),X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X26,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X29)))
        | v1_xboole_0(X29) )
      & ( v1_funct_2(k2_partfun1(X26,X29,X30,X27),X27,X28)
        | ~ r1_tarski(X27,X26)
        | ~ r1_tarski(k7_relset_1(X26,X29,X30,X27),X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X26,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X29)))
        | v1_xboole_0(X29) )
      & ( m1_subset_1(k2_partfun1(X26,X29,X30,X27),k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | ~ r1_tarski(X27,X26)
        | ~ r1_tarski(k7_relset_1(X26,X29,X30,X27),X28)
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,X26,X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X29)))
        | v1_xboole_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t178_funct_2])])])])])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),X2)
    | ~ r1_tarski(esk4_0,k2_zfmisc_1(X3,X2)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_23])).

cnf(c_0_54,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( k9_relat_1(esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_56,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_xboole_0(X2)
    | ~ r1_tarski(X4,X1)
    | ~ r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_36]),c_0_27])])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_42]),c_0_29])])).

cnf(c_0_60,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk1_0))))
    | ~ r1_tarski(X1,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_28]),c_0_29]),c_0_23])])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_58])).

fof(c_0_62,plain,(
    ! [X32] :
      ( v2_struct_0(X32)
      | ~ l1_struct_0(X32)
      | ~ v1_xboole_0(u1_struct_0(X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_63,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_64,negated_conjecture,
    ( k7_relset_1(X1,X2,esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_partfun1(X3,X4,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_59,c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | k7_relset_1(X1,X2,esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_23])])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_23])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_26])]),c_0_30]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:39:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.19/0.38  # and selection function PSelectComplexExceptRRHorn.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.19/0.38  fof(t61_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 0.19/0.38  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.19/0.38  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.19/0.38  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.19/0.38  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.38  fof(t178_funct_2, axiom, ![X1, X2, X3, X4]:(~(v1_xboole_0(X4))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,X1,X4))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X4))))=>((r1_tarski(X2,X1)&r1_tarski(k7_relset_1(X1,X4,X5,X2),X3))=>((v1_funct_1(k2_partfun1(X1,X4,X5,X2))&v1_funct_2(k2_partfun1(X1,X4,X5,X2),X2,X3))&m1_subset_1(k2_partfun1(X1,X4,X5,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 0.19/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.38  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.38  fof(c_0_12, plain, ![X6, X7]:((~m1_subset_1(X6,k1_zfmisc_1(X7))|r1_tarski(X6,X7))&(~r1_tarski(X6,X7)|m1_subset_1(X6,k1_zfmisc_1(X7)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  fof(c_0_13, plain, ![X14, X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|m1_subset_1(k7_relset_1(X14,X15,X16,X17),k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.19/0.38  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t61_tmap_1])).
% 0.19/0.38  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_16, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_17, plain, ![X18, X19, X20, X21]:(~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))|k7_relset_1(X18,X19,X20,X21)=k9_relat_1(X20,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.19/0.38  fof(c_0_18, plain, ![X33, X34, X35, X36]:(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)|(v2_struct_0(X34)|~v2_pre_topc(X34)|~l1_pre_topc(X34)|(~v1_funct_1(X35)|~v1_funct_2(X35,u1_struct_0(X33),u1_struct_0(X34))|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X33),u1_struct_0(X34))))|(~m1_pre_topc(X36,X33)|k2_tmap_1(X33,X34,X35,X36)=k2_partfun1(u1_struct_0(X33),u1_struct_0(X34),X35,u1_struct_0(X36)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.19/0.38  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(esk5_0,u1_struct_0(esk3_0))&k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.38  cnf(c_0_20, plain, (r1_tarski(k7_relset_1(X1,X2,X3,X4),X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.19/0.38  cnf(c_0_21, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_22, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_29, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_32, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25]), c_0_26]), c_0_27]), c_0_28]), c_0_29])]), c_0_30]), c_0_31])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_37, plain, ![X22, X23, X24, X25]:(~v1_funct_1(X24)|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k2_partfun1(X22,X23,X24,X25)=k7_relat_1(X24,X25)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.19/0.38  fof(c_0_38, plain, ![X8, X9, X10]:(~v1_relat_1(X8)|(~r1_tarski(X9,X10)|k9_relat_1(k7_relat_1(X8,X10),X9)=k9_relat_1(X8,X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.19/0.38  fof(c_0_39, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  cnf(c_0_40, plain, (r1_tarski(k9_relat_1(X1,X2),X3)|~r1_tarski(X1,k2_zfmisc_1(X4,X3))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.19/0.38  cnf(c_0_42, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.38  cnf(c_0_43, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.38  cnf(c_0_44, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.38  cnf(c_0_45, plain, (r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)|~r1_tarski(X3,k2_zfmisc_1(X6,X5))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_40, c_0_21])).
% 0.19/0.38  fof(c_0_46, plain, ![X37, X38]:(~l1_pre_topc(X37)|(~m1_pre_topc(X38,X37)|m1_subset_1(u1_struct_0(X38),k1_zfmisc_1(u1_struct_0(X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_29]), c_0_23])])).
% 0.19/0.38  cnf(c_0_48, plain, (k7_relset_1(X1,X2,k7_relat_1(X3,X4),X5)=k9_relat_1(X3,X5)|~v1_relat_1(X3)|~r1_tarski(X5,X4)|~m1_subset_1(k7_relat_1(X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_43, c_0_21])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_23])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_51, plain, ![X26, X27, X28, X29, X30]:(((v1_funct_1(k2_partfun1(X26,X29,X30,X27))|(~r1_tarski(X27,X26)|~r1_tarski(k7_relset_1(X26,X29,X30,X27),X28))|(~v1_funct_1(X30)|~v1_funct_2(X30,X26,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X29))))|v1_xboole_0(X29))&(v1_funct_2(k2_partfun1(X26,X29,X30,X27),X27,X28)|(~r1_tarski(X27,X26)|~r1_tarski(k7_relset_1(X26,X29,X30,X27),X28))|(~v1_funct_1(X30)|~v1_funct_2(X30,X26,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X29))))|v1_xboole_0(X29)))&(m1_subset_1(k2_partfun1(X26,X29,X30,X27),k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|(~r1_tarski(X27,X26)|~r1_tarski(k7_relset_1(X26,X29,X30,X27),X28))|(~v1_funct_1(X30)|~v1_funct_2(X30,X26,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X26,X29))))|v1_xboole_0(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t178_funct_2])])])])])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),X2)|~r1_tarski(esk4_0,k2_zfmisc_1(X3,X2))), inference(spm,[status(thm)],[c_0_45, c_0_23])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))), inference(spm,[status(thm)],[c_0_15, c_0_23])).
% 0.19/0.38  cnf(c_0_54, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (k9_relat_1(esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.19/0.38  cnf(c_0_56, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))|v1_xboole_0(X2)|~r1_tarski(X4,X1)|~r1_tarski(k7_relset_1(X1,X2,X3,X4),X5)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (r1_tarski(k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_36]), c_0_27])])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (k9_relat_1(esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(X1,X2,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_42]), c_0_29])])).
% 0.19/0.38  cnf(c_0_60, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk1_0))))|~r1_tarski(X1,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_28]), c_0_29]), c_0_23])])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (r1_tarski(u1_struct_0(esk3_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_15, c_0_58])).
% 0.19/0.38  fof(c_0_62, plain, ![X32]:(v2_struct_0(X32)|~l1_struct_0(X32)|~v1_xboole_0(u1_struct_0(X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.38  fof(c_0_63, plain, ![X31]:(~l1_pre_topc(X31)|l1_struct_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, (k7_relset_1(X1,X2,esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k2_partfun1(X3,X4,esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_59, c_0_21])).
% 0.19/0.38  cnf(c_0_65, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|m1_subset_1(k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.19/0.38  cnf(c_0_66, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.19/0.38  cnf(c_0_67, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.38  cnf(c_0_68, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))|k7_relset_1(X1,X2,esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_23])])).
% 0.19/0.38  cnf(c_0_69, plain, (v2_struct_0(X1)|~l1_pre_topc(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.19/0.38  cnf(c_0_70, negated_conjecture, (v1_xboole_0(u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_68, c_0_23])).
% 0.19/0.38  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_26])]), c_0_30]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 72
% 0.19/0.38  # Proof object clause steps            : 47
% 0.19/0.38  # Proof object formula steps           : 25
% 0.19/0.38  # Proof object conjectures             : 32
% 0.19/0.38  # Proof object clause conjectures      : 29
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 24
% 0.19/0.38  # Proof object initial formulas used   : 12
% 0.19/0.38  # Proof object generating inferences   : 23
% 0.19/0.38  # Proof object simplifying inferences  : 30
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 12
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 28
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 28
% 0.19/0.38  # Processed clauses                    : 196
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 56
% 0.19/0.38  # ...remaining for further processing  : 140
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 20
% 0.19/0.38  # Generated clauses                    : 400
% 0.19/0.38  # ...of the previous two non-trivial   : 388
% 0.19/0.38  # Contextual simplify-reflections      : 1
% 0.19/0.38  # Paramodulations                      : 400
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 0
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 91
% 0.19/0.38  #    Positive orientable unit clauses  : 19
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 6
% 0.19/0.38  #    Non-unit-clauses                  : 66
% 0.19/0.38  # Current number of unprocessed clauses: 248
% 0.19/0.38  # ...number of literals in the above   : 1127
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 49
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 2100
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 935
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 56
% 0.19/0.38  # Unit Clause-clause subsumption calls : 14
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 1
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 11964
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.044 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.049 s
% 0.19/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
