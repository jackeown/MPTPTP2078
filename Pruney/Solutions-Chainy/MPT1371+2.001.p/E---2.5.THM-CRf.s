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
% DateTime   : Thu Dec  3 11:14:15 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 602 expanded)
%              Number of clauses        :   66 ( 192 expanded)
%              Number of leaves         :   16 ( 149 expanded)
%              Depth                    :   15
%              Number of atoms          :  440 (6194 expanded)
%              Number of equality atoms :   73 ( 862 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   79 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t26_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( v1_compts_1(X1)
                  & v8_pre_topc(X2)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & v5_pre_topc(X3,X1,X2) )
               => v3_tops_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_compts_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t164_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( r1_tarski(X1,k1_relat_1(X2))
          & v2_funct_1(X2) )
       => k10_relat_1(X2,k9_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t25_compts_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( v1_compts_1(X1)
                  & v8_pre_topc(X2)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v5_pre_topc(X3,X1,X2) )
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X4,X1)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_compts_1)).

fof(t72_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v3_tops_2(X3,X1,X2)
              <=> ( k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3)
                  & ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v4_pre_topc(X4,X1)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_tops_2)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

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

fof(dt_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( v1_compts_1(X1)
                    & v8_pre_topc(X2)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X1)
                    & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3)
                    & v5_pre_topc(X3,X1,X2) )
                 => v3_tops_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t26_compts_1])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k2_relset_1(X24,X25,X26) = k2_relat_1(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_18,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))
      | k1_relset_1(X21,X22,X23) = k1_relat_1(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_19,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v1_compts_1(esk3_0)
    & v8_pre_topc(esk4_0)
    & k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0)
    & k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0)
    & v2_funct_1(esk5_0)
    & v5_pre_topc(esk5_0,esk3_0,esk4_0)
    & ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_20,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X35,X36,X37] :
      ( ( k7_relset_1(X35,X36,X37,X35) = k2_relset_1(X35,X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( k8_relset_1(X35,X36,X37,X36) = k1_relset_1(X35,X36,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_22,plain,(
    ! [X27,X28,X29,X30] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | k7_relset_1(X27,X28,X29,X30) = k9_relat_1(X29,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_23,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_relset_1(X1,X2,X3) = k2_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( k2_relset_1(X1,X2,esk5_0) = k2_struct_0(esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_32,plain,
    ( k9_relat_1(X1,X2) = k2_relset_1(X2,X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_33,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(X1,X2,esk5_0) = k2_struct_0(esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_26])])).

fof(c_0_35,plain,(
    ! [X9,X10] :
      ( ~ v1_relat_1(X10)
      | ~ v1_funct_1(X10)
      | ~ r1_tarski(X9,k1_relat_1(X10))
      | ~ v2_funct_1(X10)
      | k10_relat_1(X10,k9_relat_1(X10,X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).

cnf(c_0_36,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) = k2_struct_0(esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( k1_relat_1(esk5_0) = k2_struct_0(esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_34])).

fof(c_0_39,plain,(
    ! [X45] :
      ( ~ l1_struct_0(X45)
      | k2_struct_0(X45) = u1_struct_0(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_40,plain,(
    ! [X46] :
      ( ~ l1_pre_topc(X46)
      | l1_struct_0(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_41,plain,
    ( k10_relat_1(X1,k9_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1))
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(esk5_0,u1_struct_0(esk3_0)) = k2_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

cnf(c_0_43,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_26])).

cnf(c_0_46,negated_conjecture,
    ( k1_relat_1(esk5_0) = k2_struct_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_47,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_49,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_50,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ v2_pre_topc(X52)
      | ~ l1_pre_topc(X52)
      | v2_struct_0(X53)
      | ~ v2_pre_topc(X53)
      | ~ l1_pre_topc(X53)
      | ~ v1_funct_1(X54)
      | ~ v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))
      | ~ v1_compts_1(X52)
      | ~ v8_pre_topc(X53)
      | k2_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54) != k2_struct_0(X53)
      | ~ v5_pre_topc(X54,X52,X53)
      | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ v4_pre_topc(X55,X52)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,X55),X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_compts_1])])])])).

fof(c_0_51,plain,(
    ! [X47,X48,X49,X50] :
      ( ( k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) = k2_struct_0(X47)
        | ~ v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) = k2_struct_0(X48)
        | ~ v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( v2_funct_1(X49)
        | ~ v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( ~ v4_pre_topc(X50,X47)
        | v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,X50),X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,X50),X48)
        | v4_pre_topc(X50,X47)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))
        | ~ v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( m1_subset_1(esk2_3(X47,X48,X49),k1_zfmisc_1(u1_struct_0(X47)))
        | k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) != k2_struct_0(X47)
        | k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) != k2_struct_0(X48)
        | ~ v2_funct_1(X49)
        | v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( ~ v4_pre_topc(esk2_3(X47,X48,X49),X47)
        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,esk2_3(X47,X48,X49)),X48)
        | k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) != k2_struct_0(X47)
        | k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) != k2_struct_0(X48)
        | ~ v2_funct_1(X49)
        | v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) )
      & ( v4_pre_topc(esk2_3(X47,X48,X49),X47)
        | v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,esk2_3(X47,X48,X49)),X48)
        | k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) != k2_struct_0(X47)
        | k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49) != k2_struct_0(X48)
        | ~ v2_funct_1(X49)
        | v3_tops_2(X49,X47,X48)
        | ~ v1_funct_1(X49)
        | ~ v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48))))
        | v2_struct_0(X48)
        | ~ l1_pre_topc(X48)
        | ~ l1_pre_topc(X47) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tops_2])])])])])])).

cnf(c_0_52,negated_conjecture,
    ( k10_relat_1(esk5_0,k2_struct_0(esk4_0)) = u1_struct_0(esk3_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_53,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( v2_struct_0(X2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_compts_1(X1)
    | ~ v8_pre_topc(X2)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v5_pre_topc(X3,X1,X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( v8_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_58,negated_conjecture,
    ( v1_compts_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,negated_conjecture,
    ( v5_pre_topc(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_64,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_65,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_66,negated_conjecture,
    ( ~ v3_tops_2(esk5_0,esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_67,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k8_relset_1(X31,X32,X33,X34) = k10_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_68,negated_conjecture,
    ( k10_relat_1(esk5_0,u1_struct_0(esk4_0)) = u1_struct_0(esk3_0)
    | ~ r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_70,plain,
    ( v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | ~ v4_pre_topc(esk2_3(X1,X2,X3),X1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_71,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1),esk4_0)
    | ~ v4_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_26]),c_0_24]),c_0_57]),c_0_58]),c_0_59]),c_0_60]),c_0_61]),c_0_62]),c_0_54]),c_0_63]),c_0_44])]),c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_26]),c_0_29]),c_0_24]),c_0_62]),c_0_54]),c_0_63]),c_0_43]),c_0_44])]),c_0_66]),c_0_64])).

fof(c_0_73,plain,(
    ! [X40,X41,X42,X43] :
      ( ( ~ v5_pre_topc(X42,X40,X41)
        | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))
        | ~ v4_pre_topc(X43,X41)
        | v4_pre_topc(k8_relset_1(u1_struct_0(X40),u1_struct_0(X41),X42,X43),X40)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(X40) )
      & ( m1_subset_1(esk1_3(X40,X41,X42),k1_zfmisc_1(u1_struct_0(X41)))
        | v5_pre_topc(X42,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(X40) )
      & ( v4_pre_topc(esk1_3(X40,X41,X42),X41)
        | v5_pre_topc(X42,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(X40) )
      & ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X40),u1_struct_0(X41),X42,esk1_3(X40,X41,X42)),X40)
        | v5_pre_topc(X42,X40,X41)
        | ~ v1_funct_1(X42)
        | ~ v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41))))
        | ~ l1_pre_topc(X41)
        | ~ l1_pre_topc(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).

fof(c_0_74,plain,(
    ! [X17,X18,X19,X20] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | m1_subset_1(k7_relset_1(X17,X18,X19,X20),k1_zfmisc_1(X18)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).

cnf(c_0_75,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,negated_conjecture,
    ( k10_relat_1(esk5_0,u1_struct_0(esk4_0)) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_53]),c_0_69]),c_0_63])])).

cnf(c_0_77,plain,
    ( v4_pre_topc(esk2_3(X1,X2,X3),X1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)
    | v3_tops_2(X3,X1,X2)
    | v2_struct_0(X2)
    | k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X1)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) != k2_struct_0(X2)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_78,negated_conjecture,
    ( ~ v4_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_29]),c_0_24]),c_0_62]),c_0_54]),c_0_63]),c_0_43]),c_0_44]),c_0_26]),c_0_72])]),c_0_66]),c_0_64])).

cnf(c_0_79,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v4_pre_topc(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_80,plain,
    ( m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

cnf(c_0_81,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_82,negated_conjecture,
    ( k8_relset_1(X1,X2,esk5_0,u1_struct_0(esk4_0)) = u1_struct_0(esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_83,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_26]),c_0_29]),c_0_24]),c_0_62]),c_0_54]),c_0_63]),c_0_43]),c_0_44])]),c_0_66]),c_0_64]),c_0_78])).

cnf(c_0_84,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k7_relset_1(X5,X6,X3,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_28])).

cnf(c_0_85,plain,
    ( v4_pre_topc(k10_relat_1(X1,X2),X3)
    | ~ v4_pre_topc(X2,X4)
    | ~ v5_pre_topc(X1,X3,X4)
    | ~ v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X4))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_75])).

cnf(c_0_86,plain,
    ( m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_80,c_0_28])).

cnf(c_0_87,negated_conjecture,
    ( k1_relset_1(X1,u1_struct_0(esk4_0),esk5_0) = u1_struct_0(esk3_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,negated_conjecture,
    ( v4_pre_topc(k7_relset_1(X1,X2,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_26])])).

cnf(c_0_89,negated_conjecture,
    ( v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0)
    | ~ v4_pre_topc(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_26]),c_0_61]),c_0_62]),c_0_54]),c_0_63]),c_0_44])])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(k9_relat_1(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_86,c_0_26])).

cnf(c_0_91,negated_conjecture,
    ( k2_struct_0(esk3_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_87]),c_0_26])])).

cnf(c_0_92,negated_conjecture,
    ( v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_88,c_0_28])).

cnf(c_0_93,negated_conjecture,
    ( v4_pre_topc(X1,esk3_0)
    | ~ v4_pre_topc(k9_relat_1(esk5_0,X1),esk4_0)
    | ~ r1_tarski(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_41]),c_0_90]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_91])])).

cnf(c_0_94,negated_conjecture,
    ( v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_26])).

fof(c_0_95,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_96,negated_conjecture,
    ( ~ r1_tarski(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_78])).

cnf(c_0_97,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.45  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.030 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t26_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((((v1_compts_1(X1)&v8_pre_topc(X2))&k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))=>v3_tops_2(X3,X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_compts_1)).
% 0.20/0.45  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.45  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.45  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.20/0.45  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.20/0.45  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.45  fof(t164_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((r1_tarski(X1,k1_relat_1(X2))&v2_funct_1(X2))=>k10_relat_1(X2,k9_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 0.20/0.45  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.45  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.45  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.45  fof(t25_compts_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((v1_compts_1(X1)&v8_pre_topc(X2))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v5_pre_topc(X3,X1,X2))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X4,X1)=>v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_compts_1)).
% 0.20/0.45  fof(t72_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((~(v2_struct_0(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v3_tops_2(X3,X1,X2)<=>(((k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1)&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>(v4_pre_topc(X4,X1)<=>v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_tops_2)).
% 0.20/0.45  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.20/0.45  fof(d12_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(v5_pre_topc(X3,X1,X2)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X4,X2)=>v4_pre_topc(k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 0.20/0.45  fof(dt_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k7_relset_1(X1,X2,X3,X4),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 0.20/0.45  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.45  fof(c_0_16, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((((((v1_compts_1(X1)&v8_pre_topc(X2))&k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X1))&k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2))&v2_funct_1(X3))&v5_pre_topc(X3,X1,X2))=>v3_tops_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t26_compts_1])).
% 0.20/0.45  fof(c_0_17, plain, ![X24, X25, X26]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k2_relset_1(X24,X25,X26)=k2_relat_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.45  fof(c_0_18, plain, ![X21, X22, X23]:(~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))|k1_relset_1(X21,X22,X23)=k1_relat_1(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.45  fof(c_0_19, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))))&((((((v1_compts_1(esk3_0)&v8_pre_topc(esk4_0))&k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0))&k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0))&v2_funct_1(esk5_0))&v5_pre_topc(esk5_0,esk3_0,esk4_0))&~v3_tops_2(esk5_0,esk3_0,esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.20/0.45  cnf(c_0_20, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.45  fof(c_0_21, plain, ![X35, X36, X37]:((k7_relset_1(X35,X36,X37,X35)=k2_relset_1(X35,X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))&(k8_relset_1(X35,X36,X37,X36)=k1_relset_1(X35,X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.20/0.45  fof(c_0_22, plain, ![X27, X28, X29, X30]:(~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|k7_relset_1(X27,X28,X29,X30)=k9_relat_1(X29,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.20/0.45  cnf(c_0_23, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_24, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_25, plain, (k2_relset_1(X1,X2,X3)=k2_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_20, c_0_20])).
% 0.20/0.45  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_27, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_28, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.45  cnf(c_0_29, negated_conjecture, (k1_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_30, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_23, c_0_23])).
% 0.20/0.45  cnf(c_0_31, negated_conjecture, (k2_relset_1(X1,X2,esk5_0)=k2_struct_0(esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.45  cnf(c_0_32, plain, (k9_relat_1(X1,X2)=k2_relset_1(X2,X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.45  fof(c_0_33, plain, ![X11, X12, X13]:(~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|v1_relat_1(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.45  cnf(c_0_34, negated_conjecture, (k1_relset_1(X1,X2,esk5_0)=k2_struct_0(esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_26])])).
% 0.20/0.45  fof(c_0_35, plain, ![X9, X10]:(~v1_relat_1(X10)|~v1_funct_1(X10)|(~r1_tarski(X9,k1_relat_1(X10))|~v2_funct_1(X10)|k10_relat_1(X10,k9_relat_1(X10,X9))=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t164_funct_1])])).
% 0.20/0.45  cnf(c_0_36, negated_conjecture, (k9_relat_1(esk5_0,X1)=k2_struct_0(esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.45  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.45  cnf(c_0_38, negated_conjecture, (k1_relat_1(esk5_0)=k2_struct_0(esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_23, c_0_34])).
% 0.20/0.45  fof(c_0_39, plain, ![X45]:(~l1_struct_0(X45)|k2_struct_0(X45)=u1_struct_0(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.45  fof(c_0_40, plain, ![X46]:(~l1_pre_topc(X46)|l1_struct_0(X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.45  cnf(c_0_41, plain, (k10_relat_1(X1,k9_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~r1_tarski(X2,k1_relat_1(X1))|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.45  cnf(c_0_42, negated_conjecture, (k9_relat_1(esk5_0,u1_struct_0(esk3_0))=k2_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_36, c_0_26])).
% 0.20/0.45  cnf(c_0_43, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_44, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_26])).
% 0.20/0.45  cnf(c_0_46, negated_conjecture, (k1_relat_1(esk5_0)=k2_struct_0(esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_26])).
% 0.20/0.45  cnf(c_0_47, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.45  cnf(c_0_48, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.45  fof(c_0_49, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.45  fof(c_0_50, plain, ![X52, X53, X54, X55]:(~v2_pre_topc(X52)|~l1_pre_topc(X52)|(v2_struct_0(X53)|~v2_pre_topc(X53)|~l1_pre_topc(X53)|(~v1_funct_1(X54)|~v1_funct_2(X54,u1_struct_0(X52),u1_struct_0(X53))|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X52),u1_struct_0(X53))))|(~v1_compts_1(X52)|~v8_pre_topc(X53)|k2_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54)!=k2_struct_0(X53)|~v5_pre_topc(X54,X52,X53)|(~m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(X52)))|(~v4_pre_topc(X55,X52)|v4_pre_topc(k7_relset_1(u1_struct_0(X52),u1_struct_0(X53),X54,X55),X53))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t25_compts_1])])])])).
% 0.20/0.45  fof(c_0_51, plain, ![X47, X48, X49, X50]:(((((k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)=k2_struct_0(X47)|~v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47))&(k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)=k2_struct_0(X48)|~v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47)))&(v2_funct_1(X49)|~v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47)))&((~v4_pre_topc(X50,X47)|v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,X50),X48)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))|~v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47))&(~v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,X50),X48)|v4_pre_topc(X50,X47)|~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X47)))|~v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47))))&((m1_subset_1(esk2_3(X47,X48,X49),k1_zfmisc_1(u1_struct_0(X47)))|(k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)!=k2_struct_0(X47)|k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)!=k2_struct_0(X48)|~v2_funct_1(X49))|v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47))&((~v4_pre_topc(esk2_3(X47,X48,X49),X47)|~v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,esk2_3(X47,X48,X49)),X48)|(k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)!=k2_struct_0(X47)|k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)!=k2_struct_0(X48)|~v2_funct_1(X49))|v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47))&(v4_pre_topc(esk2_3(X47,X48,X49),X47)|v4_pre_topc(k7_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49,esk2_3(X47,X48,X49)),X48)|(k1_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)!=k2_struct_0(X47)|k2_relset_1(u1_struct_0(X47),u1_struct_0(X48),X49)!=k2_struct_0(X48)|~v2_funct_1(X49))|v3_tops_2(X49,X47,X48)|(~v1_funct_1(X49)|~v1_funct_2(X49,u1_struct_0(X47),u1_struct_0(X48))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X47),u1_struct_0(X48)))))|(v2_struct_0(X48)|~l1_pre_topc(X48))|~l1_pre_topc(X47))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_tops_2])])])])])])).
% 0.20/0.45  cnf(c_0_52, negated_conjecture, (k10_relat_1(esk5_0,k2_struct_0(esk4_0))=u1_struct_0(esk3_0)|~r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])])).
% 0.20/0.45  cnf(c_0_53, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.45  cnf(c_0_54, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_55, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.45  cnf(c_0_56, plain, (v2_struct_0(X2)|v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_compts_1(X1)|~v8_pre_topc(X2)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v5_pre_topc(X3,X1,X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~v4_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (v8_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (v1_compts_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_61, negated_conjecture, (v5_pre_topc(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_63, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_64, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  cnf(c_0_65, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|v3_tops_2(X3,X1,X2)|v2_struct_0(X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_66, negated_conjecture, (~v3_tops_2(esk5_0,esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.45  fof(c_0_67, plain, ![X31, X32, X33, X34]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k8_relset_1(X31,X32,X33,X34)=k10_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.20/0.45  cnf(c_0_68, negated_conjecture, (k10_relat_1(esk5_0,u1_struct_0(esk4_0))=u1_struct_0(esk3_0)|~r1_tarski(u1_struct_0(esk3_0),k2_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.20/0.45  cnf(c_0_69, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_55])).
% 0.20/0.45  cnf(c_0_70, plain, (v3_tops_2(X3,X1,X2)|v2_struct_0(X2)|~v4_pre_topc(esk2_3(X1,X2,X3),X1)|~v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_71, negated_conjecture, (v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,X1),esk4_0)|~v4_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_26]), c_0_24]), c_0_57]), c_0_58]), c_0_59]), c_0_60]), c_0_61]), c_0_62]), c_0_54]), c_0_63]), c_0_44])]), c_0_64])).
% 0.20/0.45  cnf(c_0_72, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_26]), c_0_29]), c_0_24]), c_0_62]), c_0_54]), c_0_63]), c_0_43]), c_0_44])]), c_0_66]), c_0_64])).
% 0.20/0.45  fof(c_0_73, plain, ![X40, X41, X42, X43]:((~v5_pre_topc(X42,X40,X41)|(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X41)))|(~v4_pre_topc(X43,X41)|v4_pre_topc(k8_relset_1(u1_struct_0(X40),u1_struct_0(X41),X42,X43),X40)))|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41)))))|~l1_pre_topc(X41)|~l1_pre_topc(X40))&((m1_subset_1(esk1_3(X40,X41,X42),k1_zfmisc_1(u1_struct_0(X41)))|v5_pre_topc(X42,X40,X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41)))))|~l1_pre_topc(X41)|~l1_pre_topc(X40))&((v4_pre_topc(esk1_3(X40,X41,X42),X41)|v5_pre_topc(X42,X40,X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41)))))|~l1_pre_topc(X41)|~l1_pre_topc(X40))&(~v4_pre_topc(k8_relset_1(u1_struct_0(X40),u1_struct_0(X41),X42,esk1_3(X40,X41,X42)),X40)|v5_pre_topc(X42,X40,X41)|(~v1_funct_1(X42)|~v1_funct_2(X42,u1_struct_0(X40),u1_struct_0(X41))|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X40),u1_struct_0(X41)))))|~l1_pre_topc(X41)|~l1_pre_topc(X40))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_pre_topc])])])])])).
% 0.20/0.45  fof(c_0_74, plain, ![X17, X18, X19, X20]:(~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))|m1_subset_1(k7_relset_1(X17,X18,X19,X20),k1_zfmisc_1(X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relset_1])])).
% 0.20/0.45  cnf(c_0_75, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.20/0.45  cnf(c_0_76, negated_conjecture, (k10_relat_1(esk5_0,u1_struct_0(esk4_0))=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_53]), c_0_69]), c_0_63])])).
% 0.20/0.45  cnf(c_0_77, plain, (v4_pre_topc(esk2_3(X1,X2,X3),X1)|v4_pre_topc(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk2_3(X1,X2,X3)),X2)|v3_tops_2(X3,X1,X2)|v2_struct_0(X2)|k1_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X1)|k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)!=k2_struct_0(X2)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.45  cnf(c_0_78, negated_conjecture, (~v4_pre_topc(esk2_3(esk3_0,esk4_0,esk5_0),esk3_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_29]), c_0_24]), c_0_62]), c_0_54]), c_0_63]), c_0_43]), c_0_44]), c_0_26]), c_0_72])]), c_0_66]), c_0_64])).
% 0.20/0.45  cnf(c_0_79, plain, (v4_pre_topc(k8_relset_1(u1_struct_0(X2),u1_struct_0(X3),X1,X4),X2)|~v5_pre_topc(X1,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~v4_pre_topc(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.20/0.45  cnf(c_0_80, plain, (m1_subset_1(k7_relset_1(X2,X3,X1,X4),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_74])).
% 0.20/0.45  cnf(c_0_81, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.45  cnf(c_0_82, negated_conjecture, (k8_relset_1(X1,X2,esk5_0,u1_struct_0(esk4_0))=u1_struct_0(esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.45  cnf(c_0_83, negated_conjecture, (v4_pre_topc(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_26]), c_0_29]), c_0_24]), c_0_62]), c_0_54]), c_0_63]), c_0_43]), c_0_44])]), c_0_66]), c_0_64]), c_0_78])).
% 0.20/0.45  cnf(c_0_84, plain, (k7_relset_1(X1,X2,X3,X4)=k7_relset_1(X5,X6,X3,X4)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_28, c_0_28])).
% 0.20/0.45  cnf(c_0_85, plain, (v4_pre_topc(k10_relat_1(X1,X2),X3)|~v4_pre_topc(X2,X4)|~v5_pre_topc(X1,X3,X4)|~v1_funct_2(X1,u1_struct_0(X3),u1_struct_0(X4))|~l1_pre_topc(X4)|~l1_pre_topc(X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))), inference(spm,[status(thm)],[c_0_79, c_0_75])).
% 0.20/0.45  cnf(c_0_86, plain, (m1_subset_1(k9_relat_1(X1,X2),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_80, c_0_28])).
% 0.20/0.45  cnf(c_0_87, negated_conjecture, (k1_relset_1(X1,u1_struct_0(esk4_0),esk5_0)=u1_struct_0(esk3_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.20/0.45  cnf(c_0_88, negated_conjecture, (v4_pre_topc(k7_relset_1(X1,X2,esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_26])])).
% 0.20/0.45  cnf(c_0_89, negated_conjecture, (v4_pre_topc(k10_relat_1(esk5_0,X1),esk3_0)|~v4_pre_topc(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_26]), c_0_61]), c_0_62]), c_0_54]), c_0_63]), c_0_44])])).
% 0.20/0.45  cnf(c_0_90, negated_conjecture, (m1_subset_1(k9_relat_1(esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_86, c_0_26])).
% 0.20/0.45  cnf(c_0_91, negated_conjecture, (k2_struct_0(esk3_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_87]), c_0_26])])).
% 0.20/0.45  cnf(c_0_92, negated_conjecture, (v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_88, c_0_28])).
% 0.20/0.45  cnf(c_0_93, negated_conjecture, (v4_pre_topc(X1,esk3_0)|~v4_pre_topc(k9_relat_1(esk5_0,X1),esk4_0)|~r1_tarski(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_41]), c_0_90]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_91])])).
% 0.20/0.45  cnf(c_0_94, negated_conjecture, (v4_pre_topc(k9_relat_1(esk5_0,esk2_3(esk3_0,esk4_0,esk5_0)),esk4_0)), inference(spm,[status(thm)],[c_0_92, c_0_26])).
% 0.20/0.45  fof(c_0_95, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.45  cnf(c_0_96, negated_conjecture, (~r1_tarski(esk2_3(esk3_0,esk4_0,esk5_0),u1_struct_0(esk3_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_78])).
% 0.20/0.45  cnf(c_0_97, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_95])).
% 0.20/0.45  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_72])]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 99
% 0.20/0.45  # Proof object clause steps            : 66
% 0.20/0.45  # Proof object formula steps           : 33
% 0.20/0.45  # Proof object conjectures             : 43
% 0.20/0.45  # Proof object clause conjectures      : 40
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 33
% 0.20/0.45  # Proof object initial formulas used   : 16
% 0.20/0.45  # Proof object generating inferences   : 32
% 0.20/0.45  # Proof object simplifying inferences  : 80
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 18
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 48
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 48
% 0.20/0.45  # Processed clauses                    : 542
% 0.20/0.45  # ...of these trivial                  : 9
% 0.20/0.45  # ...subsumed                          : 221
% 0.20/0.45  # ...remaining for further processing  : 312
% 0.20/0.45  # Other redundant clauses eliminated   : 2
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 10
% 0.20/0.45  # Backward-rewritten                   : 7
% 0.20/0.45  # Generated clauses                    : 1223
% 0.20/0.45  # ...of the previous two non-trivial   : 1166
% 0.20/0.45  # Contextual simplify-reflections      : 8
% 0.20/0.45  # Paramodulations                      : 1221
% 0.20/0.45  # Factorizations                       : 0
% 0.20/0.45  # Equation resolutions                 : 2
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 246
% 0.20/0.45  #    Positive orientable unit clauses  : 57
% 0.20/0.45  #    Positive unorientable unit clauses: 0
% 0.20/0.45  #    Negative unit clauses             : 4
% 0.20/0.45  #    Non-unit-clauses                  : 185
% 0.20/0.45  # Current number of unprocessed clauses: 704
% 0.20/0.45  # ...number of literals in the above   : 3889
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 64
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 30645
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 4959
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 215
% 0.20/0.45  # Unit Clause-clause subsumption calls : 361
% 0.20/0.45  # Rewrite failures with RHS unbound    : 0
% 0.20/0.45  # BW rewrite match attempts            : 11
% 0.20/0.45  # BW rewrite match successes           : 5
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 43702
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.098 s
% 0.20/0.45  # System time              : 0.007 s
% 0.20/0.45  # Total time               : 0.105 s
% 0.20/0.45  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
