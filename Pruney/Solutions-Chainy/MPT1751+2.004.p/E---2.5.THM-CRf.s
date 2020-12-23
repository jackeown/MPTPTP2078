%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:22 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 154 expanded)
%              Number of clauses        :   39 (  57 expanded)
%              Number of leaves         :   13 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  201 (1084 expanded)
%              Number of equality atoms :   24 (  87 expanded)
%              Maximal formula depth    :   16 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tmap_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(t99_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(t87_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(t162_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( r1_tarski(X2,X3)
         => k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_13,negated_conjecture,(
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

fof(c_0_14,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_15,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_17,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k7_relset_1(X26,X27,X28,X29) = k9_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_18,plain,(
    ! [X37,X38,X39,X40] :
      ( v2_struct_0(X37)
      | ~ v2_pre_topc(X37)
      | ~ l1_pre_topc(X37)
      | v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | ~ v1_funct_1(X39)
      | ~ v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))
      | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))
      | ~ m1_pre_topc(X40,X37)
      | k2_tmap_1(X37,X38,X39,X40) = k2_partfun1(u1_struct_0(X37),u1_struct_0(X38),X39,u1_struct_0(X40)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_19,plain,(
    ! [X9,X10] :
      ( ( ~ v5_relat_1(X10,X9)
        | r1_tarski(k2_relat_1(X10),X9)
        | ~ v1_relat_1(X10) )
      & ( ~ r1_tarski(k2_relat_1(X10),X9)
        | v5_relat_1(X10,X9)
        | ~ v1_relat_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_20,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X33,X34,X35,X36] :
      ( ~ v1_funct_1(X35)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
      | k2_partfun1(X33,X34,X35,X36) = k7_relat_1(X35,X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_25,plain,
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

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_34,plain,(
    ! [X6,X7,X8] :
      ( ~ r1_tarski(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r1_tarski(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_35,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v5_relat_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21])).

cnf(c_0_38,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0) != k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_21])).

cnf(c_0_40,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_41,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1)) = k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31])]),c_0_32]),c_0_33])).

fof(c_0_42,plain,(
    ! [X30,X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(k1_relat_1(X32),X30)
      | ~ r1_tarski(k2_relat_1(X32),X31)
      | m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

fof(c_0_45,plain,(
    ! [X18,X19] :
      ( ~ v1_relat_1(X19)
      | r1_tarski(k2_relat_1(k7_relat_1(X19,X18)),k2_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).

cnf(c_0_46,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0) != k9_relat_1(esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k2_tmap_1(esk2_0,esk1_0,esk4_0,X1) = k7_relat_1(esk4_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31]),c_0_21])])).

cnf(c_0_48,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_49,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,k2_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_53,plain,
    ( k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(k2_relat_1(X3),X2)
    | ~ r1_tarski(k1_relat_1(X3),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_37])])).

fof(c_0_55,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X17)
      | r1_tarski(k1_relat_1(k7_relat_1(X17,X16)),X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).

cnf(c_0_56,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_57,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_58,plain,(
    ! [X13,X14,X15] :
      ( ~ v1_relat_1(X13)
      | ~ r1_tarski(X14,X15)
      | k9_relat_1(k7_relat_1(X13,X15),X14) = k9_relat_1(X13,X14) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).

cnf(c_0_59,negated_conjecture,
    ( k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0) != k9_relat_1(esk4_0,esk5_0)
    | ~ v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_37])])).

cnf(c_0_60,plain,
    ( k9_relat_1(k7_relat_1(X1,X3),X2) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_62,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | v1_relat_1(k7_relat_1(X11,X12)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_37]),c_0_61])])).

cnf(c_0_64,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 19:26:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.18/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.18/0.36  # and selection function PSelectComplexExceptRRHorn.
% 0.18/0.36  #
% 0.18/0.36  # Preprocessing time       : 0.028 s
% 0.18/0.36  # Presaturation interreduction done
% 0.18/0.36  
% 0.18/0.36  # Proof found!
% 0.18/0.36  # SZS status Theorem
% 0.18/0.36  # SZS output start CNFRefutation
% 0.18/0.36  fof(t61_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_tmap_1)).
% 0.18/0.36  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.18/0.36  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.18/0.36  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.18/0.36  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.18/0.36  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.18/0.36  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 0.18/0.36  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.18/0.36  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 0.18/0.36  fof(t99_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k2_relat_1(k7_relat_1(X2,X1)),k2_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 0.18/0.36  fof(t87_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k1_relat_1(k7_relat_1(X2,X1)),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 0.18/0.36  fof(t162_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(r1_tarski(X2,X3)=>k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 0.18/0.36  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.18/0.36  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X2))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X5]:(m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))=>(r1_tarski(X5,u1_struct_0(X3))=>k7_relset_1(u1_struct_0(X2),u1_struct_0(X1),X4,X5)=k7_relset_1(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)))))))), inference(assume_negation,[status(cth)],[t61_tmap_1])).
% 0.18/0.36  fof(c_0_14, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.18/0.36  fof(c_0_15, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk2_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(r1_tarski(esk5_0,u1_struct_0(esk3_0))&k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.18/0.36  fof(c_0_16, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.18/0.36  fof(c_0_17, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k7_relset_1(X26,X27,X28,X29)=k9_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.18/0.36  fof(c_0_18, plain, ![X37, X38, X39, X40]:(v2_struct_0(X37)|~v2_pre_topc(X37)|~l1_pre_topc(X37)|(v2_struct_0(X38)|~v2_pre_topc(X38)|~l1_pre_topc(X38)|(~v1_funct_1(X39)|~v1_funct_2(X39,u1_struct_0(X37),u1_struct_0(X38))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X37),u1_struct_0(X38))))|(~m1_pre_topc(X40,X37)|k2_tmap_1(X37,X38,X39,X40)=k2_partfun1(u1_struct_0(X37),u1_struct_0(X38),X39,u1_struct_0(X40)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.18/0.36  fof(c_0_19, plain, ![X9, X10]:((~v5_relat_1(X10,X9)|r1_tarski(k2_relat_1(X10),X9)|~v1_relat_1(X10))&(~r1_tarski(k2_relat_1(X10),X9)|v5_relat_1(X10,X9)|~v1_relat_1(X10))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.18/0.36  cnf(c_0_20, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.18/0.36  cnf(c_0_21, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_22, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.18/0.36  cnf(c_0_23, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.18/0.36  fof(c_0_24, plain, ![X33, X34, X35, X36]:(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))|k2_partfun1(X33,X34,X35,X36)=k7_relat_1(X35,X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 0.18/0.36  cnf(c_0_25, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.18/0.36  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_27, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_28, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_31, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  fof(c_0_34, plain, ![X6, X7, X8]:(~r1_tarski(X6,X7)|~r1_tarski(X7,X8)|r1_tarski(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.18/0.36  cnf(c_0_35, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.18/0.36  cnf(c_0_36, negated_conjecture, (v5_relat_1(esk4_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.18/0.36  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_22, c_0_21])).
% 0.18/0.36  cnf(c_0_38, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,esk5_0)!=k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_39, negated_conjecture, (k7_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,X1)=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_23, c_0_21])).
% 0.18/0.36  cnf(c_0_40, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.18/0.36  cnf(c_0_41, negated_conjecture, (k2_partfun1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),esk4_0,u1_struct_0(X1))=k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)|~m1_pre_topc(X1,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_26]), c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31])]), c_0_32]), c_0_33])).
% 0.18/0.36  fof(c_0_42, plain, ![X30, X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(k1_relat_1(X32),X30)|~r1_tarski(k2_relat_1(X32),X31)|m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 0.18/0.36  cnf(c_0_43, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.18/0.36  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])])).
% 0.18/0.36  fof(c_0_45, plain, ![X18, X19]:(~v1_relat_1(X19)|r1_tarski(k2_relat_1(k7_relat_1(X19,X18)),k2_relat_1(X19))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t99_relat_1])])).
% 0.18/0.36  cnf(c_0_46, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k2_tmap_1(esk2_0,esk1_0,esk4_0,esk3_0),esk5_0)!=k9_relat_1(esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_38, c_0_39])).
% 0.18/0.36  cnf(c_0_47, negated_conjecture, (k2_tmap_1(esk2_0,esk1_0,esk4_0,X1)=k7_relat_1(esk4_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31]), c_0_21])])).
% 0.18/0.36  cnf(c_0_48, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  cnf(c_0_49, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.18/0.36  cnf(c_0_50, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk1_0))|~r1_tarski(X1,k2_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.18/0.36  cnf(c_0_51, plain, (r1_tarski(k2_relat_1(k7_relat_1(X1,X2)),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.18/0.36  cnf(c_0_52, negated_conjecture, (k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk1_0),k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.18/0.36  cnf(c_0_53, plain, (k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)|~v1_relat_1(X3)|~r1_tarski(k2_relat_1(X3),X2)|~r1_tarski(k1_relat_1(X3),X1)), inference(spm,[status(thm)],[c_0_23, c_0_49])).
% 0.18/0.36  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_relat_1(k7_relat_1(esk4_0,X1)),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_37])])).
% 0.18/0.36  fof(c_0_55, plain, ![X16, X17]:(~v1_relat_1(X17)|r1_tarski(k1_relat_1(k7_relat_1(X17,X16)),X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t87_relat_1])])).
% 0.18/0.36  cnf(c_0_56, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))|~r1_tarski(k1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0))),u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.18/0.36  cnf(c_0_57, plain, (r1_tarski(k1_relat_1(k7_relat_1(X1,X2)),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.18/0.36  fof(c_0_58, plain, ![X13, X14, X15]:(~v1_relat_1(X13)|(~r1_tarski(X14,X15)|k9_relat_1(k7_relat_1(X13,X15),X14)=k9_relat_1(X13,X14))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t162_relat_1])])])).
% 0.18/0.36  cnf(c_0_59, negated_conjecture, (k9_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)),esk5_0)!=k9_relat_1(esk4_0,esk5_0)|~v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_37])])).
% 0.18/0.36  cnf(c_0_60, plain, (k9_relat_1(k7_relat_1(X1,X3),X2)=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.18/0.36  cnf(c_0_61, negated_conjecture, (r1_tarski(esk5_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.18/0.36  fof(c_0_62, plain, ![X11, X12]:(~v1_relat_1(X11)|v1_relat_1(k7_relat_1(X11,X12))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.18/0.36  cnf(c_0_63, negated_conjecture, (~v1_relat_1(k7_relat_1(esk4_0,u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_37]), c_0_61])])).
% 0.18/0.36  cnf(c_0_64, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.18/0.36  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_37])]), ['proof']).
% 0.18/0.36  # SZS output end CNFRefutation
% 0.18/0.36  # Proof object total steps             : 66
% 0.18/0.36  # Proof object clause steps            : 39
% 0.18/0.36  # Proof object formula steps           : 27
% 0.18/0.36  # Proof object conjectures             : 29
% 0.18/0.36  # Proof object clause conjectures      : 26
% 0.18/0.36  # Proof object formula conjectures     : 3
% 0.18/0.36  # Proof object initial clauses used    : 24
% 0.18/0.36  # Proof object initial formulas used   : 13
% 0.18/0.36  # Proof object generating inferences   : 14
% 0.18/0.36  # Proof object simplifying inferences  : 28
% 0.18/0.36  # Training examples: 0 positive, 0 negative
% 0.18/0.36  # Parsed axioms                        : 13
% 0.18/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.36  # Initial clauses                      : 28
% 0.18/0.36  # Removed in clause preprocessing      : 0
% 0.18/0.36  # Initial clauses in saturation        : 28
% 0.18/0.36  # Processed clauses                    : 98
% 0.18/0.36  # ...of these trivial                  : 0
% 0.18/0.36  # ...subsumed                          : 4
% 0.18/0.36  # ...remaining for further processing  : 94
% 0.18/0.36  # Other redundant clauses eliminated   : 0
% 0.18/0.36  # Clauses deleted for lack of memory   : 0
% 0.18/0.36  # Backward-subsumed                    : 1
% 0.18/0.36  # Backward-rewritten                   : 2
% 0.18/0.36  # Generated clauses                    : 62
% 0.18/0.36  # ...of the previous two non-trivial   : 61
% 0.18/0.36  # Contextual simplify-reflections      : 1
% 0.18/0.36  # Paramodulations                      : 62
% 0.18/0.36  # Factorizations                       : 0
% 0.18/0.36  # Equation resolutions                 : 0
% 0.18/0.36  # Propositional unsat checks           : 0
% 0.18/0.36  #    Propositional check models        : 0
% 0.18/0.36  #    Propositional check unsatisfiable : 0
% 0.18/0.36  #    Propositional clauses             : 0
% 0.18/0.36  #    Propositional clauses after purity: 0
% 0.18/0.36  #    Propositional unsat core size     : 0
% 0.18/0.36  #    Propositional preprocessing time  : 0.000
% 0.18/0.36  #    Propositional encoding time       : 0.000
% 0.18/0.36  #    Propositional solver time         : 0.000
% 0.18/0.36  #    Success case prop preproc time    : 0.000
% 0.18/0.36  #    Success case prop encoding time   : 0.000
% 0.18/0.36  #    Success case prop solver time     : 0.000
% 0.18/0.36  # Current number of processed clauses  : 63
% 0.18/0.36  #    Positive orientable unit clauses  : 17
% 0.18/0.36  #    Positive unorientable unit clauses: 0
% 0.18/0.36  #    Negative unit clauses             : 6
% 0.18/0.36  #    Non-unit-clauses                  : 40
% 0.18/0.36  # Current number of unprocessed clauses: 19
% 0.18/0.36  # ...number of literals in the above   : 74
% 0.18/0.36  # Current number of archived formulas  : 0
% 0.18/0.36  # Current number of archived clauses   : 31
% 0.18/0.36  # Clause-clause subsumption calls (NU) : 435
% 0.18/0.36  # Rec. Clause-clause subsumption calls : 202
% 0.18/0.36  # Non-unit clause-clause subsumptions  : 6
% 0.18/0.36  # Unit Clause-clause subsumption calls : 4
% 0.18/0.36  # Rewrite failures with RHS unbound    : 0
% 0.18/0.36  # BW rewrite match attempts            : 2
% 0.18/0.36  # BW rewrite match successes           : 2
% 0.18/0.36  # Condensation attempts                : 0
% 0.18/0.36  # Condensation successes               : 0
% 0.18/0.36  # Termbank termtop insertions          : 3783
% 0.18/0.36  
% 0.18/0.36  # -------------------------------------------------
% 0.18/0.36  # User time                : 0.034 s
% 0.18/0.36  # System time              : 0.003 s
% 0.18/0.36  # Total time               : 0.037 s
% 0.18/0.36  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
