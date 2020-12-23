%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:24 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 159 expanded)
%              Number of clauses        :   39 (  58 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :  208 (1122 expanded)
%              Number of equality atoms :   22 (  91 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

fof(c_0_12,negated_conjecture,(
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

fof(c_0_13,plain,(
    ! [X35,X36,X37,X38] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ v2_pre_topc(X36)
      | ~ l1_pre_topc(X36)
      | ~ v1_funct_1(X37)
      | ~ v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X36))
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X36))))
      | ~ m1_pre_topc(X38,X35)
      | k2_tmap_1(X35,X36,X37,X38) = k2_partfun1(u1_struct_0(X35),u1_struct_0(X36),X37,u1_struct_0(X38)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_14,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X27,X28,X29,X30] :
      ( ( v1_funct_1(k2_partfun1(X27,X28,X29,X30))
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) )
      & ( m1_subset_1(k2_partfun1(X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
        | ~ v1_funct_1(X29)
        | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

fof(c_0_16,plain,(
    ! [X31,X32,X33,X34] :
      ( ~ v1_funct_1(X33)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_partfun1(X31,X32,X33,X34) = k7_relat_1(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

fof(c_0_17,plain,(
    ! [X20,X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | k7_relset_1(X20,X21,X22,X23) = k9_relat_1(X22,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_18,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_relat_1(X26)
      | ~ r1_tarski(k1_relat_1(X26),X24)
      | ~ r1_tarski(k2_relat_1(X26),X25)
      | m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_29,plain,(
    ! [X15,X16] :
      ( ~ v1_relat_1(X16)
      | r1_tarski(k1_relat_1(k7_relat_1(X16,X15)),X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

fof(c_0_30,plain,(
    ! [X17,X18,X19] :
      ( ( v4_relat_1(X19,X17)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v5_relat_1(X19,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_33,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_34,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_35,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_36,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_40,plain,(
    ! [X8,X9] :
      ( ( ~ v5_relat_1(X9,X8)
        | r1_tarski(k2_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k2_relat_1(X9),X8)
        | v5_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_41,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_43,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,negated_conjecture,
    ( k9_relat_1(k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_37]),c_0_25]),c_0_19])])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_48,plain,(
    ! [X12,X13,X14] :
      ( ~ v1_relat_1(X12)
      | ~ r1_tarski(X13,X14)
      | k9_relat_1(k7_relat_1(X12,X14),X13) = k9_relat_1(X12,X13) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_49,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_50,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_42]),c_0_44])])).

cnf(c_0_53,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_54,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_19]),c_0_44])])).

cnf(c_0_57,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk4_0,X1),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_19]),c_0_25])])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(k7_relat_1(esk4_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_19]),c_0_25])])).

cnf(c_0_60,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k9_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_63,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_36]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:58:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.12/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.027 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(t61_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 0.12/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.12/0.39  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.12/0.39  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.12/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.12/0.39  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 0.12/0.39  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 0.12/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.12/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.12/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.12/0.39  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.12/0.39  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 0.12/0.39  fof(c_0_12, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t61_tmap_1])).
% 0.12/0.39  fof(c_0_13, plain, ![X35, X36, X37, X38]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(v2_struct_0(X36)|~v2_pre_topc(X36)|~l1_pre_topc(X36)|(~v1_funct_1(X37)|~v1_funct_2(X37,u1_struct_0(X35),u1_struct_0(X36))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X35),u1_struct_0(X36))))|(~m1_pre_topc(X38,X35)|k2_tmap_1(X35,X36,X37,X38)=k2_partfun1(u1_struct_0(X35),u1_struct_0(X36),X37,u1_struct_0(X38)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.12/0.39  fof(c_0_14, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(esk5_0,u1_struct_0(esk3_0))&k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).
% 0.12/0.39  fof(c_0_15, plain, ![X27, X28, X29, X30]:((v1_funct_1(k2_partfun1(X27,X28,X29,X30))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))&(m1_subset_1(k2_partfun1(X27,X28,X29,X30),k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|(~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.12/0.39  fof(c_0_16, plain, ![X31, X32, X33, X34]:(~v1_funct_1(X33)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k2_partfun1(X31,X32,X33,X34)=k7_relat_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.12/0.39  fof(c_0_17, plain, ![X20, X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|k7_relset_1(X20,X21,X22,X23)=k9_relat_1(X22,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.12/0.39  cnf(c_0_18, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_23, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_25, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  fof(c_0_28, plain, ![X24, X25, X26]:(~v1_relat_1(X26)|(~r1_tarski(k1_relat_1(X26),X24)|~r1_tarski(k2_relat_1(X26),X25)|m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.12/0.39  fof(c_0_29, plain, ![X15, X16]:(~v1_relat_1(X16)|r1_tarski(k1_relat_1(k7_relat_1(X16,X15)),X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.12/0.39  fof(c_0_30, plain, ![X17, X18, X19]:((v4_relat_1(X19,X17)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))&(v5_relat_1(X19,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.12/0.39  cnf(c_0_31, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.39  cnf(c_0_32, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.39  fof(c_0_33, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.12/0.39  fof(c_0_34, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.12/0.39  cnf(c_0_35, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_36, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20]), c_0_21]), c_0_22]), c_0_23]), c_0_24]), c_0_25])]), c_0_26]), c_0_27])).
% 0.12/0.39  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.39  cnf(c_0_39, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.39  fof(c_0_40, plain, ![X8, X9]:((~v5_relat_1(X9,X8)|r1_tarski(k2_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k2_relat_1(X9),X8)|v5_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.12/0.39  cnf(c_0_41, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.12/0.39  cnf(c_0_42, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.12/0.39  cnf(c_0_43, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.12/0.39  cnf(c_0_44, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.12/0.39  cnf(c_0_45, negated_conjecture, (k9_relat_1(k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_37]), c_0_25]), c_0_19])])).
% 0.12/0.39  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  fof(c_0_48, plain, ![X12, X13, X14]:(~v1_relat_1(X12)|(~r1_tarski(X13,X14)|k9_relat_1(k7_relat_1(X12,X14),X13)=k9_relat_1(X12,X13))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.12/0.39  cnf(c_0_49, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),X3)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.12/0.39  cnf(c_0_50, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.39  cnf(c_0_51, plain, (v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X4,X3)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.39  cnf(c_0_52, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_42]), c_0_44])])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)|~m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.12/0.39  cnf(c_0_54, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_19]), c_0_44])])).
% 0.12/0.39  cnf(c_0_57, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.12/0.39  cnf(c_0_58, negated_conjecture, (v5_relat_1(k7_relat_1(esk4_0,X1),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_19]), c_0_25])])).
% 0.12/0.39  cnf(c_0_59, negated_conjecture, (v1_relat_1(k7_relat_1(esk4_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_19]), c_0_25])])).
% 0.12/0.39  cnf(c_0_60, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~m1_subset_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])])).
% 0.12/0.39  cnf(c_0_61, negated_conjecture, (m1_subset_1(k7_relat_1(esk4_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_56])])).
% 0.12/0.39  cnf(c_0_62, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k9_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.12/0.39  cnf(c_0_63, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_36]), c_0_19])]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 64
% 0.12/0.39  # Proof object clause steps            : 39
% 0.12/0.39  # Proof object formula steps           : 25
% 0.12/0.39  # Proof object conjectures             : 26
% 0.12/0.39  # Proof object clause conjectures      : 23
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 23
% 0.12/0.39  # Proof object initial formulas used   : 12
% 0.12/0.39  # Proof object generating inferences   : 15
% 0.12/0.39  # Proof object simplifying inferences  : 32
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 12
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 28
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 28
% 0.12/0.39  # Processed clauses                    : 228
% 0.12/0.39  # ...of these trivial                  : 1
% 0.12/0.39  # ...subsumed                          : 72
% 0.12/0.39  # ...remaining for further processing  : 155
% 0.12/0.39  # Other redundant clauses eliminated   : 0
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 2
% 0.12/0.39  # Backward-rewritten                   : 6
% 0.12/0.39  # Generated clauses                    : 241
% 0.12/0.39  # ...of the previous two non-trivial   : 232
% 0.12/0.39  # Contextual simplify-reflections      : 30
% 0.12/0.39  # Paramodulations                      : 241
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 0
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 119
% 0.12/0.39  #    Positive orientable unit clauses  : 20
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 7
% 0.12/0.39  #    Non-unit-clauses                  : 92
% 0.12/0.39  # Current number of unprocessed clauses: 60
% 0.12/0.39  # ...number of literals in the above   : 319
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 36
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 5989
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 2175
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 104
% 0.12/0.39  # Unit Clause-clause subsumption calls : 142
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 9
% 0.12/0.39  # BW rewrite match successes           : 5
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 10157
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.044 s
% 0.12/0.39  # System time              : 0.004 s
% 0.12/0.39  # Total time               : 0.048 s
% 0.12/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
