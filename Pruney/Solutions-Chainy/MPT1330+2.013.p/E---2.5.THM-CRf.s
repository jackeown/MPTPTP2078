%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:28 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 501 expanded)
%              Number of clauses        :   63 ( 212 expanded)
%              Number of leaves         :   18 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  236 (1955 expanded)
%              Number of equality atoms :   91 ( 686 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t52_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_struct_0(X2) = k1_xboole_0
                 => k2_struct_0(X1) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(t79_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k2_relat_1(X2),X1)
       => k5_relat_1(X2,k6_relat_1(X1)) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(t132_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | v1_partfun1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(t182_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc3_funct_1,axiom,(
    ! [X1] :
      ( v1_relat_1(k6_relat_1(X1))
      & v1_funct_1(k6_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(redefinition_k8_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k8_relset_1(X1,X2,X3,X4) = k10_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(t171_funct_2,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => k8_relset_1(X1,X1,k6_partfun1(X1),X2) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_struct_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_struct_0(X2) = k1_xboole_0
                   => k2_struct_0(X1) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2)) = k2_struct_0(X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t52_tops_2])).

fof(c_0_19,plain,(
    ! [X38] :
      ( ~ l1_struct_0(X38)
      | k2_struct_0(X38) = u1_struct_0(X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_20,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ( k2_struct_0(esk2_0) != k1_xboole_0
      | k2_struct_0(esk1_0) = k1_xboole_0 )
    & k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0)) != k2_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | ~ r1_tarski(k2_relat_1(X18),X17)
      | k5_relat_1(X18,k6_relat_1(X17)) = X18 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).

fof(c_0_22,plain,(
    ! [X11,X12] :
      ( ( ~ v5_relat_1(X12,X11)
        | r1_tarski(k2_relat_1(X12),X11)
        | ~ v1_relat_1(X12) )
      & ( ~ r1_tarski(k2_relat_1(X12),X11)
        | v5_relat_1(X12,X11)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_23,plain,(
    ! [X23,X24,X25] :
      ( ( v4_relat_1(X25,X23)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( v5_relat_1(X25,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))
      | v1_relat_1(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_25,plain,(
    ! [X33,X34,X35] :
      ( ( X34 = k1_xboole_0
        | v1_partfun1(X35,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) )
      & ( X33 != k1_xboole_0
        | v1_partfun1(X35,X33)
        | ~ v1_funct_1(X35)
        | ~ v1_funct_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))
        | ~ v1_funct_1(X35)
        | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_26,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X14)
      | ~ v1_relat_1(X15)
      | k1_relat_1(k5_relat_1(X14,X15)) = k10_relat_1(X14,k1_relat_1(X15)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).

cnf(c_0_30,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X16] :
      ( k1_relat_1(k6_relat_1(X16)) = X16
      & k2_relat_1(k6_relat_1(X16)) = X16 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

fof(c_0_33,plain,(
    ! [X19] :
      ( v1_relat_1(k6_relat_1(X19))
      & v1_funct_1(k6_relat_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[fc3_funct_1])).

fof(c_0_34,plain,(
    ! [X30,X31] :
      ( ( ~ v1_partfun1(X31,X30)
        | k1_relat_1(X31) = X30
        | ~ v1_relat_1(X31)
        | ~ v4_relat_1(X31,X30) )
      & ( k1_relat_1(X31) != X30
        | v1_partfun1(X31,X30)
        | ~ v1_relat_1(X31)
        | ~ v4_relat_1(X31,X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_35,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0)) != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_41,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_28])).

fof(c_0_42,plain,(
    ! [X26,X27,X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
      | k8_relset_1(X26,X27,X28,X29) = k10_relat_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).

cnf(c_0_43,plain,
    ( k1_relat_1(k5_relat_1(X1,X2)) = k10_relat_1(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k5_relat_1(X1,k6_relat_1(X2)) = X1
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_46,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_49,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_38])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk2_0)) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_55,plain,
    ( k8_relset_1(X2,X3,X1,X4) = k10_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_56,plain,
    ( k10_relat_1(X1,X2) = k1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),c_0_46])])).

cnf(c_0_57,negated_conjecture,
    ( v5_relat_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_47,c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( k2_struct_0(esk1_0) = k1_xboole_0
    | k2_struct_0(esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_59,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | ~ v1_partfun1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_partfun1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_36]),c_0_52]),c_0_53])])).

cnf(c_0_61,negated_conjecture,
    ( k10_relat_1(esk3_0,u1_struct_0(esk2_0)) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_36])])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk3_0,u1_struct_0(esk2_0)) = k1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_50])])).

fof(c_0_63,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(X36))
      | k8_relset_1(X36,X36,k6_partfun1(X36),X37) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).

fof(c_0_64,plain,(
    ! [X32] : k6_partfun1(X32) = k6_relat_1(X32) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_65,negated_conjecture,
    ( k2_struct_0(esk1_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_58,c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk3_0) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,plain,
    ( k8_relset_1(X2,X2,k6_partfun1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_69,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

fof(c_0_70,plain,(
    ! [X5,X6] :
      ( ( k2_zfmisc_1(X5,X6) != k1_xboole_0
        | X5 = k1_xboole_0
        | X6 = k1_xboole_0 )
      & ( X5 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X5,X6) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( k8_relset_1(X2,X2,k6_relat_1(X2),X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

fof(c_0_75,plain,(
    ! [X13] : k10_relat_1(k1_xboole_0,X13) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

cnf(c_0_76,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_77,plain,(
    ! [X7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_79,plain,
    ( v1_partfun1(X1,X2)
    | k1_relat_1(X1) != X2
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_80,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_72])])).

cnf(c_0_81,plain,
    ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_84,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_77])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_86,plain,
    ( v1_partfun1(X1,k1_relat_1(X1))
    | ~ v4_relat_1(X1,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_79])).

cnf(c_0_87,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_45,c_0_74])).

cnf(c_0_88,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_74])).

cnf(c_0_89,negated_conjecture,
    ( v4_relat_1(esk3_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_80])).

cnf(c_0_90,negated_conjecture,
    ( k1_relat_1(esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_80])).

cnf(c_0_91,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_81]),c_0_82]),c_0_83]),c_0_84])])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_72]),c_0_85])).

cnf(c_0_93,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | ~ v4_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])])).

cnf(c_0_94,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_84])).

cnf(c_0_95,negated_conjecture,
    ( ~ v1_partfun1(esk3_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_89]),c_0_50])]),c_0_90])).

cnf(c_0_96,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_97,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_94])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:39:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t52_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 0.14/0.38  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.14/0.38  fof(t79_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(k2_relat_1(X2),X1)=>k5_relat_1(X2,k6_relat_1(X1))=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 0.14/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.14/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.38  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 0.14/0.38  fof(t182_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 0.14/0.38  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.14/0.38  fof(fc3_funct_1, axiom, ![X1]:(v1_relat_1(k6_relat_1(X1))&v1_funct_1(k6_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 0.14/0.38  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.14/0.38  fof(redefinition_k8_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k8_relset_1(X1,X2,X3,X4)=k10_relat_1(X3,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 0.14/0.38  fof(t171_funct_2, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>k8_relset_1(X1,X1,k6_partfun1(X1),X2)=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_2)).
% 0.14/0.38  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.14/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 0.14/0.38  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 0.14/0.38  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.38  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t52_tops_2])).
% 0.14/0.38  fof(c_0_19, plain, ![X38]:(~l1_struct_0(X38)|k2_struct_0(X38)=u1_struct_0(X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.14/0.38  fof(c_0_20, negated_conjecture, (l1_struct_0(esk1_0)&(l1_struct_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_struct_0(esk2_0)!=k1_xboole_0|k2_struct_0(esk1_0)=k1_xboole_0)&k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0))!=k2_struct_0(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.14/0.38  fof(c_0_21, plain, ![X17, X18]:(~v1_relat_1(X18)|(~r1_tarski(k2_relat_1(X18),X17)|k5_relat_1(X18,k6_relat_1(X17))=X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t79_relat_1])])).
% 0.14/0.38  fof(c_0_22, plain, ![X11, X12]:((~v5_relat_1(X12,X11)|r1_tarski(k2_relat_1(X12),X11)|~v1_relat_1(X12))&(~r1_tarski(k2_relat_1(X12),X11)|v5_relat_1(X12,X11)|~v1_relat_1(X12))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.14/0.38  fof(c_0_23, plain, ![X23, X24, X25]:((v4_relat_1(X25,X23)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))&(v5_relat_1(X25,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.38  fof(c_0_24, plain, ![X20, X21, X22]:(~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))|v1_relat_1(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.38  fof(c_0_25, plain, ![X33, X34, X35]:((X34=k1_xboole_0|v1_partfun1(X35,X33)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))|(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))&(X33!=k1_xboole_0|v1_partfun1(X35,X33)|(~v1_funct_1(X35)|~v1_funct_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34))))|(~v1_funct_1(X35)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X33,X34)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.14/0.38  cnf(c_0_26, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  cnf(c_0_27, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_28, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  fof(c_0_29, plain, ![X14, X15]:(~v1_relat_1(X14)|(~v1_relat_1(X15)|k1_relat_1(k5_relat_1(X14,X15))=k10_relat_1(X14,k1_relat_1(X15)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t182_relat_1])])])).
% 0.14/0.38  cnf(c_0_30, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_31, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.38  fof(c_0_32, plain, ![X16]:(k1_relat_1(k6_relat_1(X16))=X16&k2_relat_1(k6_relat_1(X16))=X16), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.14/0.38  fof(c_0_33, plain, ![X19]:(v1_relat_1(k6_relat_1(X19))&v1_funct_1(k6_relat_1(X19))), inference(variable_rename,[status(thm)],[fc3_funct_1])).
% 0.14/0.38  fof(c_0_34, plain, ![X30, X31]:((~v1_partfun1(X31,X30)|k1_relat_1(X31)=X30|(~v1_relat_1(X31)|~v4_relat_1(X31,X30)))&(k1_relat_1(X31)!=X30|v1_partfun1(X31,X30)|(~v1_relat_1(X31)|~v4_relat_1(X31,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.14/0.38  cnf(c_0_35, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.38  cnf(c_0_38, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0))!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_40, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.14/0.38  cnf(c_0_41, negated_conjecture, (k2_struct_0(esk1_0)=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_26, c_0_28])).
% 0.14/0.38  fof(c_0_42, plain, ![X26, X27, X28, X29]:(~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))|k8_relset_1(X26,X27,X28,X29)=k10_relat_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k8_relset_1])])).
% 0.14/0.38  cnf(c_0_43, plain, (k1_relat_1(k5_relat_1(X1,X2))=k10_relat_1(X1,k1_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.38  cnf(c_0_44, plain, (k5_relat_1(X1,k6_relat_1(X2))=X1|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.14/0.38  cnf(c_0_45, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.14/0.38  cnf(c_0_46, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.38  cnf(c_0_48, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 0.14/0.38  cnf(c_0_51, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_38])).
% 0.14/0.38  cnf(c_0_52, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk2_0))!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.14/0.38  cnf(c_0_55, plain, (k8_relset_1(X2,X3,X1,X4)=k10_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.38  cnf(c_0_56, plain, (k10_relat_1(X1,X2)=k1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), c_0_46])])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (v5_relat_1(esk3_0,u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_47, c_0_36])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, (k2_struct_0(esk1_0)=k1_xboole_0|k2_struct_0(esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.38  cnf(c_0_59, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|~v1_partfun1(esk3_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.14/0.38  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_partfun1(esk3_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_36]), c_0_52]), c_0_53])])).
% 0.14/0.38  cnf(c_0_61, negated_conjecture, (k10_relat_1(esk3_0,u1_struct_0(esk2_0))!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_36])])).
% 0.14/0.38  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk3_0,u1_struct_0(esk2_0))=k1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_50])])).
% 0.14/0.38  fof(c_0_63, plain, ![X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(X36))|k8_relset_1(X36,X36,k6_partfun1(X36),X37)=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t171_funct_2])])).
% 0.14/0.38  fof(c_0_64, plain, ![X32]:k6_partfun1(X32)=k6_relat_1(X32), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.14/0.38  cnf(c_0_65, negated_conjecture, (k2_struct_0(esk1_0)=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_58, c_0_40])).
% 0.14/0.38  cnf(c_0_66, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.14/0.38  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk3_0)!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[c_0_61, c_0_62])).
% 0.14/0.38  cnf(c_0_68, plain, (k8_relset_1(X2,X2,k6_partfun1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.14/0.38  cnf(c_0_69, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.14/0.38  fof(c_0_70, plain, ![X5, X6]:((k2_zfmisc_1(X5,X6)!=k1_xboole_0|(X5=k1_xboole_0|X6=k1_xboole_0))&((X5!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0)&(X6!=k1_xboole_0|k2_zfmisc_1(X5,X6)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.14/0.38  cnf(c_0_71, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_65])).
% 0.14/0.38  cnf(c_0_72, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_66, c_0_67])).
% 0.14/0.38  cnf(c_0_73, plain, (k8_relset_1(X2,X2,k6_relat_1(X2),X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.14/0.38  cnf(c_0_74, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.14/0.38  fof(c_0_75, plain, ![X13]:k10_relat_1(k1_xboole_0,X13)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.14/0.38  cnf(c_0_76, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.14/0.38  fof(c_0_77, plain, ![X7]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.38  cnf(c_0_78, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.14/0.38  cnf(c_0_79, plain, (v1_partfun1(X1,X2)|k1_relat_1(X1)!=X2|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.38  cnf(c_0_80, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_72])])).
% 0.14/0.38  cnf(c_0_81, plain, (k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X1)=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.14/0.38  cnf(c_0_82, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.14/0.38  cnf(c_0_83, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_76])).
% 0.14/0.38  cnf(c_0_84, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_77])).
% 0.14/0.38  cnf(c_0_85, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_78])).
% 0.14/0.38  cnf(c_0_86, plain, (v1_partfun1(X1,k1_relat_1(X1))|~v4_relat_1(X1,k1_relat_1(X1))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_79])).
% 0.14/0.38  cnf(c_0_87, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_45, c_0_74])).
% 0.14/0.38  cnf(c_0_88, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_74])).
% 0.14/0.38  cnf(c_0_89, negated_conjecture, (v4_relat_1(esk3_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_49, c_0_80])).
% 0.14/0.38  cnf(c_0_90, negated_conjecture, (k1_relat_1(esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_67, c_0_80])).
% 0.14/0.38  cnf(c_0_91, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_81]), c_0_82]), c_0_83]), c_0_84])])).
% 0.14/0.38  cnf(c_0_92, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_72]), c_0_85])).
% 0.14/0.38  cnf(c_0_93, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)|~v4_relat_1(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])])).
% 0.14/0.38  cnf(c_0_94, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_35, c_0_84])).
% 0.14/0.38  cnf(c_0_95, negated_conjecture, (~v1_partfun1(esk3_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_89]), c_0_50])]), c_0_90])).
% 0.14/0.38  cnf(c_0_96, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.14/0.38  cnf(c_0_97, plain, (v1_partfun1(k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93, c_0_94])])).
% 0.14/0.38  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96]), c_0_97])]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 99
% 0.14/0.38  # Proof object clause steps            : 63
% 0.14/0.38  # Proof object formula steps           : 36
% 0.14/0.38  # Proof object conjectures             : 32
% 0.14/0.38  # Proof object clause conjectures      : 29
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 27
% 0.14/0.38  # Proof object initial formulas used   : 18
% 0.14/0.38  # Proof object generating inferences   : 21
% 0.14/0.38  # Proof object simplifying inferences  : 42
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 19
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 33
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 32
% 0.14/0.38  # Processed clauses                    : 135
% 0.14/0.38  # ...of these trivial                  : 4
% 0.14/0.38  # ...subsumed                          : 7
% 0.14/0.38  # ...remaining for further processing  : 124
% 0.14/0.38  # Other redundant clauses eliminated   : 4
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 1
% 0.14/0.38  # Backward-rewritten                   : 25
% 0.14/0.38  # Generated clauses                    : 88
% 0.14/0.38  # ...of the previous two non-trivial   : 84
% 0.14/0.38  # Contextual simplify-reflections      : 2
% 0.14/0.38  # Paramodulations                      : 83
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 4
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 61
% 0.14/0.38  #    Positive orientable unit clauses  : 26
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 0
% 0.14/0.38  #    Non-unit-clauses                  : 35
% 0.14/0.38  # Current number of unprocessed clauses: 12
% 0.14/0.38  # ...number of literals in the above   : 30
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 60
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 174
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 108
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.14/0.38  # Unit Clause-clause subsumption calls : 69
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 6
% 0.14/0.38  # BW rewrite match successes           : 6
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 3265
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.003 s
% 0.14/0.38  # Total time               : 0.037 s
% 0.14/0.38  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
