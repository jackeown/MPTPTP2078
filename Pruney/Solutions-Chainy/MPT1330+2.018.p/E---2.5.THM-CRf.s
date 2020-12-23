%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:29 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 318 expanded)
%              Number of clauses        :   48 ( 133 expanded)
%              Number of leaves         :   16 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 (1150 expanded)
%              Number of equality atoms :   52 ( 393 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(cc5_funct_2,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
         => ( ( v1_funct_1(X3)
              & v1_funct_2(X3,X1,X2) )
           => ( v1_funct_1(X3)
              & v1_partfun1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X2)
     => v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t29_relset_1,axiom,(
    ! [X1] : m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X34] :
      ( ~ l1_struct_0(X34)
      | k2_struct_0(X34) = u1_struct_0(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_18,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & ( k2_struct_0(esk2_0) != k1_xboole_0
      | k2_struct_0(esk1_0) = k1_xboole_0 )
    & k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0)) != k2_struct_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_19,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0)) != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( k2_struct_0(esk1_0) = u1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_21])).

fof(c_0_25,plain,(
    ! [X26,X27,X28] :
      ( ( k7_relset_1(X26,X27,X28,X26) = k2_relset_1(X26,X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( k8_relset_1(X26,X27,X28,X27) = k1_relset_1(X26,X27,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

fof(c_0_26,plain,(
    ! [X29,X30,X31] :
      ( ( v1_funct_1(X31)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | v1_xboole_0(X30) )
      & ( v1_partfun1(X31,X29)
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,X29,X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
        | v1_xboole_0(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] :
      ( ( v4_relat_1(X21,X19)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( v5_relat_1(X21,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_28,plain,(
    ! [X10,X11] :
      ( ~ v1_relat_1(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X10))
      | v1_relat_1(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_29,plain,(
    ! [X14,X15] : v1_relat_1(k2_zfmisc_1(X14,X15)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_30,negated_conjecture,
    ( k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk2_0)) != u1_struct_0(esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24])).

cnf(c_0_31,plain,
    ( k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_33,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_34,plain,(
    ! [X32,X33] :
      ( ( ~ v1_partfun1(X33,X32)
        | k1_relat_1(X33) = X32
        | ~ v1_relat_1(X33)
        | ~ v4_relat_1(X33,X32) )
      & ( k1_relat_1(X33) != X32
        | v1_partfun1(X33,X32)
        | ~ v1_relat_1(X33)
        | ~ v4_relat_1(X33,X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_35,plain,
    ( v1_partfun1(X1,X2)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])])).

cnf(c_0_42,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X4] :
      ( ~ v1_xboole_0(X4)
      | X4 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

fof(c_0_44,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X7)
      | v1_xboole_0(k2_zfmisc_1(X6,X7)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).

cnf(c_0_45,negated_conjecture,
    ( k2_struct_0(esk1_0) = k1_xboole_0
    | k2_struct_0(esk2_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,negated_conjecture,
    ( v1_partfun1(esk3_0,u1_struct_0(esk1_0))
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_32]),c_0_36]),c_0_37])])).

cnf(c_0_48,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_40])])).

cnf(c_0_50,negated_conjecture,
    ( k1_relat_1(esk3_0) != u1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_32])])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k2_zfmisc_1(X2,X1))
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( k2_struct_0(esk1_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_23])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])]),c_0_50])).

fof(c_0_55,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,k1_xboole_0)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_56,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_59,plain,(
    ! [X25] : m1_subset_1(k6_relat_1(X25),k1_zfmisc_1(k2_zfmisc_1(X25,X25))) ),
    inference(variable_rename,[status(thm)],[t29_relset_1])).

cnf(c_0_60,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0
    | u1_struct_0(esk2_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_53])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_54])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_64,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_65,plain,(
    ! [X12,X13] :
      ( ( ~ v4_relat_1(X13,X12)
        | r1_tarski(k1_relat_1(X13),X12)
        | ~ v1_relat_1(X13) )
      & ( ~ r1_tarski(k1_relat_1(X13),X12)
        | v4_relat_1(X13,X12)
        | ~ v1_relat_1(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_66,plain,
    ( m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_61])])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_61]),c_0_64])).

cnf(c_0_70,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,plain,
    ( m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_64])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk3_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_50,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v4_relat_1(X1,k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_70])).

cnf(c_0_75,plain,
    ( v4_relat_1(k6_relat_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_66])).

cnf(c_0_76,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_68,c_0_71])).

cnf(c_0_77,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_64])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_79,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_76]),c_0_77])]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.37  #
% 0.19/0.37  # Preprocessing time       : 0.028 s
% 0.19/0.37  # Presaturation interreduction done
% 0.19/0.37  
% 0.19/0.37  # Proof found!
% 0.19/0.37  # SZS status Theorem
% 0.19/0.37  # SZS output start CNFRefutation
% 0.19/0.37  fof(t52_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_tops_2)).
% 0.19/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.37  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 0.19/0.37  fof(cc5_funct_2, axiom, ![X1, X2]:(~(v1_xboole_0(X2))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))=>(v1_funct_1(X3)&v1_partfun1(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 0.19/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.37  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 0.19/0.37  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.19/0.37  fof(fc3_zfmisc_1, axiom, ![X1, X2]:(v1_xboole_0(X2)=>v1_xboole_0(k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 0.19/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.37  fof(t29_relset_1, axiom, ![X1]:m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 0.19/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.37  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_struct_0(X2)=k1_xboole_0=>k2_struct_0(X1)=k1_xboole_0)=>k8_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,k2_struct_0(X2))=k2_struct_0(X1)))))), inference(assume_negation,[status(cth)],[t52_tops_2])).
% 0.19/0.37  fof(c_0_17, plain, ![X34]:(~l1_struct_0(X34)|k2_struct_0(X34)=u1_struct_0(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.37  fof(c_0_18, negated_conjecture, (l1_struct_0(esk1_0)&(l1_struct_0(esk2_0)&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_struct_0(esk2_0)!=k1_xboole_0|k2_struct_0(esk1_0)=k1_xboole_0)&k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0))!=k2_struct_0(esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.37  cnf(c_0_19, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.37  cnf(c_0_20, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_21, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_22, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,k2_struct_0(esk2_0))!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_23, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.37  cnf(c_0_24, negated_conjecture, (k2_struct_0(esk1_0)=u1_struct_0(esk1_0)), inference(spm,[status(thm)],[c_0_19, c_0_21])).
% 0.19/0.37  fof(c_0_25, plain, ![X26, X27, X28]:((k7_relset_1(X26,X27,X28,X26)=k2_relset_1(X26,X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))&(k8_relset_1(X26,X27,X28,X27)=k1_relset_1(X26,X27,X28)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.19/0.37  fof(c_0_26, plain, ![X29, X30, X31]:((v1_funct_1(X31)|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X30))&(v1_partfun1(X31,X29)|(~v1_funct_1(X31)|~v1_funct_2(X31,X29,X30))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_xboole_0(X30))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc5_funct_2])])])])])).
% 0.19/0.37  fof(c_0_27, plain, ![X19, X20, X21]:((v4_relat_1(X21,X19)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))&(v5_relat_1(X21,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.37  fof(c_0_28, plain, ![X10, X11]:(~v1_relat_1(X10)|(~m1_subset_1(X11,k1_zfmisc_1(X10))|v1_relat_1(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.37  fof(c_0_29, plain, ![X14, X15]:v1_relat_1(k2_zfmisc_1(X14,X15)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.37  cnf(c_0_30, negated_conjecture, (k8_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,u1_struct_0(esk2_0))!=u1_struct_0(esk1_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24])).
% 0.19/0.37  cnf(c_0_31, plain, (k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.37  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  fof(c_0_33, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|k1_relset_1(X22,X23,X24)=k1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.37  fof(c_0_34, plain, ![X32, X33]:((~v1_partfun1(X33,X32)|k1_relat_1(X33)=X32|(~v1_relat_1(X33)|~v4_relat_1(X33,X32)))&(k1_relat_1(X33)!=X32|v1_partfun1(X33,X32)|(~v1_relat_1(X33)|~v4_relat_1(X33,X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.19/0.37  cnf(c_0_35, plain, (v1_partfun1(X1,X2)|v1_xboole_0(X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.37  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_38, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.37  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.37  cnf(c_0_40, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.37  cnf(c_0_41, negated_conjecture, (k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])])).
% 0.19/0.37  cnf(c_0_42, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.19/0.37  fof(c_0_43, plain, ![X4]:(~v1_xboole_0(X4)|X4=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.19/0.37  fof(c_0_44, plain, ![X6, X7]:(~v1_xboole_0(X7)|v1_xboole_0(k2_zfmisc_1(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc3_zfmisc_1])])).
% 0.19/0.37  cnf(c_0_45, negated_conjecture, (k2_struct_0(esk1_0)=k1_xboole_0|k2_struct_0(esk2_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.37  cnf(c_0_46, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.37  cnf(c_0_47, negated_conjecture, (v1_partfun1(esk3_0,u1_struct_0(esk1_0))|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_32]), c_0_36]), c_0_37])])).
% 0.19/0.37  cnf(c_0_48, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 0.19/0.37  cnf(c_0_49, negated_conjecture, (v1_relat_1(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_40])])).
% 0.19/0.37  cnf(c_0_50, negated_conjecture, (k1_relat_1(esk3_0)!=u1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_32])])).
% 0.19/0.37  cnf(c_0_51, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.37  cnf(c_0_52, plain, (v1_xboole_0(k2_zfmisc_1(X2,X1))|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.37  cnf(c_0_53, negated_conjecture, (k2_struct_0(esk1_0)=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_23])).
% 0.19/0.37  cnf(c_0_54, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])]), c_0_50])).
% 0.19/0.37  fof(c_0_55, plain, ![X5]:(~r1_tarski(X5,k1_xboole_0)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.37  fof(c_0_56, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.37  cnf(c_0_57, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.37  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.37  fof(c_0_59, plain, ![X25]:m1_subset_1(k6_relat_1(X25),k1_zfmisc_1(k2_zfmisc_1(X25,X25))), inference(variable_rename,[status(thm)],[t29_relset_1])).
% 0.19/0.37  cnf(c_0_60, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0|u1_struct_0(esk2_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_53])).
% 0.19/0.37  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_54])).
% 0.19/0.37  cnf(c_0_62, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.19/0.37  cnf(c_0_63, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.19/0.37  cnf(c_0_64, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.37  fof(c_0_65, plain, ![X12, X13]:((~v4_relat_1(X13,X12)|r1_tarski(k1_relat_1(X13),X12)|~v1_relat_1(X13))&(~r1_tarski(k1_relat_1(X13),X12)|v4_relat_1(X13,X12)|~v1_relat_1(X13))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.37  cnf(c_0_66, plain, (m1_subset_1(k6_relat_1(X1),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.37  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_61])])).
% 0.19/0.37  cnf(c_0_68, plain, (X1=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.19/0.37  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_61]), c_0_64])).
% 0.19/0.37  cnf(c_0_70, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.37  cnf(c_0_71, plain, (m1_subset_1(k6_relat_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_66, c_0_64])).
% 0.19/0.37  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk3_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_50, c_0_67])).
% 0.19/0.37  cnf(c_0_73, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.37  cnf(c_0_74, plain, (k1_relat_1(X1)=k1_xboole_0|~v4_relat_1(X1,k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_70])).
% 0.19/0.37  cnf(c_0_75, plain, (v4_relat_1(k6_relat_1(X1),X1)), inference(spm,[status(thm)],[c_0_38, c_0_66])).
% 0.19/0.37  cnf(c_0_76, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_68, c_0_71])).
% 0.19/0.37  cnf(c_0_77, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_40, c_0_64])).
% 0.19/0.37  cnf(c_0_78, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_72, c_0_73])).
% 0.19/0.37  cnf(c_0_79, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_75]), c_0_76]), c_0_76]), c_0_77])]), c_0_78]), ['proof']).
% 0.19/0.37  # SZS output end CNFRefutation
% 0.19/0.37  # Proof object total steps             : 80
% 0.19/0.37  # Proof object clause steps            : 48
% 0.19/0.37  # Proof object formula steps           : 32
% 0.19/0.37  # Proof object conjectures             : 27
% 0.19/0.37  # Proof object clause conjectures      : 24
% 0.19/0.37  # Proof object formula conjectures     : 3
% 0.19/0.37  # Proof object initial clauses used    : 22
% 0.19/0.37  # Proof object initial formulas used   : 16
% 0.19/0.37  # Proof object generating inferences   : 20
% 0.19/0.37  # Proof object simplifying inferences  : 27
% 0.19/0.37  # Training examples: 0 positive, 0 negative
% 0.19/0.37  # Parsed axioms                        : 18
% 0.19/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.37  # Initial clauses                      : 30
% 0.19/0.37  # Removed in clause preprocessing      : 1
% 0.19/0.37  # Initial clauses in saturation        : 29
% 0.19/0.37  # Processed clauses                    : 109
% 0.19/0.37  # ...of these trivial                  : 2
% 0.19/0.37  # ...subsumed                          : 4
% 0.19/0.37  # ...remaining for further processing  : 103
% 0.19/0.37  # Other redundant clauses eliminated   : 1
% 0.19/0.37  # Clauses deleted for lack of memory   : 0
% 0.19/0.37  # Backward-subsumed                    : 0
% 0.19/0.37  # Backward-rewritten                   : 24
% 0.19/0.37  # Generated clauses                    : 51
% 0.19/0.37  # ...of the previous two non-trivial   : 57
% 0.19/0.37  # Contextual simplify-reflections      : 0
% 0.19/0.37  # Paramodulations                      : 50
% 0.19/0.37  # Factorizations                       : 0
% 0.19/0.37  # Equation resolutions                 : 1
% 0.19/0.37  # Propositional unsat checks           : 0
% 0.19/0.37  #    Propositional check models        : 0
% 0.19/0.37  #    Propositional check unsatisfiable : 0
% 0.19/0.37  #    Propositional clauses             : 0
% 0.19/0.37  #    Propositional clauses after purity: 0
% 0.19/0.37  #    Propositional unsat core size     : 0
% 0.19/0.37  #    Propositional preprocessing time  : 0.000
% 0.19/0.37  #    Propositional encoding time       : 0.000
% 0.19/0.37  #    Propositional solver time         : 0.000
% 0.19/0.37  #    Success case prop preproc time    : 0.000
% 0.19/0.37  #    Success case prop encoding time   : 0.000
% 0.19/0.37  #    Success case prop solver time     : 0.000
% 0.19/0.37  # Current number of processed clauses  : 49
% 0.19/0.37  #    Positive orientable unit clauses  : 22
% 0.19/0.37  #    Positive unorientable unit clauses: 0
% 0.19/0.37  #    Negative unit clauses             : 3
% 0.19/0.37  #    Non-unit-clauses                  : 24
% 0.19/0.37  # Current number of unprocessed clauses: 4
% 0.19/0.37  # ...number of literals in the above   : 12
% 0.19/0.37  # Current number of archived formulas  : 0
% 0.19/0.37  # Current number of archived clauses   : 53
% 0.19/0.37  # Clause-clause subsumption calls (NU) : 91
% 0.19/0.37  # Rec. Clause-clause subsumption calls : 32
% 0.19/0.37  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.37  # Unit Clause-clause subsumption calls : 87
% 0.19/0.37  # Rewrite failures with RHS unbound    : 0
% 0.19/0.37  # BW rewrite match attempts            : 6
% 0.19/0.37  # BW rewrite match successes           : 6
% 0.19/0.37  # Condensation attempts                : 0
% 0.19/0.37  # Condensation successes               : 0
% 0.19/0.37  # Termbank termtop insertions          : 2558
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
