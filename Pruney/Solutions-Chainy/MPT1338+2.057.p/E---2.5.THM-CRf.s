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
% DateTime   : Thu Dec  3 11:13:39 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 246 expanded)
%              Number of clauses        :   43 (  84 expanded)
%              Number of leaves         :   14 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  256 (1579 expanded)
%              Number of equality atoms :  106 ( 494 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t62_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_struct_0(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t31_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(t35_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => ( X2 = k1_xboole_0
          | ( k5_relat_1(X3,k2_funct_1(X3)) = k6_partfun1(X1)
            & k5_relat_1(k2_funct_1(X3),X3) = k6_partfun1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(t58_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
          & k2_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(t71_relat_1,axiom,(
    ! [X1] :
      ( k1_relat_1(k6_relat_1(X1)) = X1
      & k2_relat_1(k6_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_struct_0(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3) )
                 => ( k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X2)
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t62_tops_2])).

fof(c_0_15,plain,(
    ! [X25,X26,X27] :
      ( ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,X25,X26)
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) != X26
      | ~ v2_funct_1(X27)
      | k2_tops_2(X25,X26,X27) = k2_funct_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

fof(c_0_16,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk2_0)
      | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

cnf(c_0_17,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_23,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_relset_1(X10,X11,X12) = k1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_24,plain,(
    ! [X17,X18,X19] :
      ( ( v1_funct_1(k2_funct_1(X19))
        | ~ v2_funct_1(X19)
        | k2_relset_1(X17,X18,X19) != X18
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( v1_funct_2(k2_funct_1(X19),X18,X17)
        | ~ v2_funct_1(X19)
        | k2_relset_1(X17,X18,X19) != X18
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) )
      & ( m1_subset_1(k2_funct_1(X19),k1_zfmisc_1(k2_zfmisc_1(X18,X17)))
        | ~ v2_funct_1(X19)
        | k2_relset_1(X17,X18,X19) != X18
        | ~ v1_funct_1(X19)
        | ~ v1_funct_2(X19,X17,X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_25,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk2_0)
    | k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_funct_1(esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_27,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_29,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | k2_relset_1(X13,X14,X15) = k2_relat_1(X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_30,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)) != k2_struct_0(esk1_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,plain,
    ( k1_relset_1(X1,X2,k2_funct_1(X3)) = k1_relat_1(k2_funct_1(X3))
    | k2_relset_1(X2,X1,X3) != X1
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(pm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_30,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = k1_relat_1(k2_funct_1(esk3_0))
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_35,plain,
    ( k2_relset_1(X1,X2,k2_funct_1(X3)) = k2_relat_1(k2_funct_1(X3))
    | k2_relset_1(X2,X1,X3) != X1
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3) ),
    inference(pm,[status(thm)],[c_0_32,c_0_28])).

fof(c_0_36,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_relat_1(X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_37,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k1_relat_1(k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) = k2_relat_1(k2_funct_1(esk3_0))
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

fof(c_0_39,plain,(
    ! [X5] :
      ( ( k2_relat_1(X5) = k1_relat_1(k2_funct_1(X5))
        | ~ v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) )
      & ( k1_relat_1(X5) = k2_relat_1(k2_funct_1(X5))
        | ~ v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_40,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_41,plain,(
    ! [X20,X21,X22] :
      ( ( k5_relat_1(X22,k2_funct_1(X22)) = k6_partfun1(X20)
        | X21 = k1_xboole_0
        | k2_relset_1(X20,X21,X22) != X21
        | ~ v2_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) )
      & ( k5_relat_1(k2_funct_1(X22),X22) = k6_partfun1(X21)
        | X21 = k1_xboole_0
        | k2_relset_1(X20,X21,X22) != X21
        | ~ v2_funct_1(X22)
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X20,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).

fof(c_0_42,plain,(
    ! [X16] : k6_partfun1(X16) = k6_relat_1(X16) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

cnf(c_0_43,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) != k2_struct_0(esk1_0)
    | k1_relat_1(k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(pm,[status(thm)],[c_0_40,c_0_18])).

cnf(c_0_46,plain,
    ( k5_relat_1(X1,k2_funct_1(X1)) = k6_partfun1(X2)
    | X3 = k1_xboole_0
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_47,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk3_0)) != k2_struct_0(esk2_0)
    | k2_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43,c_0_44]),c_0_21]),c_0_22]),c_0_45])])).

cnf(c_0_49,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32,c_0_18]),c_0_19])).

fof(c_0_51,plain,(
    ! [X23] :
      ( ~ l1_struct_0(X23)
      | k2_struct_0(X23) = u1_struct_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_52,plain,(
    ! [X6] :
      ( ( k1_relat_1(k5_relat_1(X6,k2_funct_1(X6))) = k1_relat_1(X6)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( k2_relat_1(k5_relat_1(X6,k2_funct_1(X6))) = k1_relat_1(X6)
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).

cnf(c_0_53,plain,
    ( X3 = k1_xboole_0
    | k5_relat_1(X1,k2_funct_1(X1)) = k6_relat_1(X2)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_54,plain,(
    ! [X4] :
      ( k1_relat_1(k6_relat_1(X4)) = X4
      & k2_relat_1(k6_relat_1(X4)) = X4 ) ),
    inference(variable_rename,[status(thm)],[t71_relat_1])).

cnf(c_0_55,negated_conjecture,
    ( k2_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_21]),c_0_22]),c_0_45])])).

cnf(c_0_56,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( l1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_58,plain,
    ( k1_relat_1(k5_relat_1(X1,k2_funct_1(X1))) = k1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k5_relat_1(esk3_0,k2_funct_1(esk3_0)) = k6_relat_1(u1_struct_0(esk1_0))
    | u1_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_60,plain,
    ( k1_relat_1(k6_relat_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk1_0) != k1_relat_1(esk3_0)
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk1_0) = k1_relat_1(esk3_0)
    | u1_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_21]),c_0_22]),c_0_45])])).

fof(c_0_63,plain,(
    ! [X24] :
      ( v2_struct_0(X24)
      | ~ l1_struct_0(X24)
      | ~ v1_xboole_0(u1_struct_0(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_struct_0(esk2_0) != u1_struct_0(esk2_0) ),
    inference(pm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_67,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64,c_0_56]),c_0_65])])).

cnf(c_0_68,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_65])]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:17:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.37  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.12/0.37  # and selection function NoSelection.
% 0.12/0.37  #
% 0.12/0.37  # Preprocessing time       : 0.028 s
% 0.12/0.37  
% 0.12/0.37  # Proof found!
% 0.12/0.37  # SZS status Theorem
% 0.12/0.37  # SZS output start CNFRefutation
% 0.12/0.37  fof(t62_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_2)).
% 0.12/0.37  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.12/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.12/0.37  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.12/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.12/0.37  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.12/0.37  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.12/0.37  fof(t35_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>(X2=k1_xboole_0|(k5_relat_1(X3,k2_funct_1(X3))=k6_partfun1(X1)&k5_relat_1(k2_funct_1(X3),X3)=k6_partfun1(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 0.12/0.37  fof(redefinition_k6_partfun1, axiom, ![X1]:k6_partfun1(X1)=k6_relat_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 0.12/0.37  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.12/0.37  fof(t58_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)&k2_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 0.12/0.37  fof(t71_relat_1, axiom, ![X1]:(k1_relat_1(k6_relat_1(X1))=X1&k2_relat_1(k6_relat_1(X1))=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 0.12/0.37  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.12/0.37  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.37  fof(c_0_14, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>(k1_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X2)&k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3))=k2_struct_0(X1))))))), inference(assume_negation,[status(cth)],[t62_tops_2])).
% 0.12/0.37  fof(c_0_15, plain, ![X25, X26, X27]:(~v1_funct_1(X27)|~v1_funct_2(X27,X25,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))|(k2_relset_1(X25,X26,X27)!=X26|~v2_funct_1(X27)|k2_tops_2(X25,X26,X27)=k2_funct_1(X27))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.12/0.37  fof(c_0_16, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)&v2_funct_1(esk3_0))&(k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.12/0.37  cnf(c_0_17, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.37  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_19, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_20, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_21, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  fof(c_0_23, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|k1_relset_1(X10,X11,X12)=k1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.12/0.37  fof(c_0_24, plain, ![X17, X18, X19]:(((v1_funct_1(k2_funct_1(X19))|(~v2_funct_1(X19)|k2_relset_1(X17,X18,X19)!=X18)|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))&(v1_funct_2(k2_funct_1(X19),X18,X17)|(~v2_funct_1(X19)|k2_relset_1(X17,X18,X19)!=X18)|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))))))&(m1_subset_1(k2_funct_1(X19),k1_zfmisc_1(k2_zfmisc_1(X18,X17)))|(~v2_funct_1(X19)|k2_relset_1(X17,X18,X19)!=X18)|(~v1_funct_1(X19)|~v1_funct_2(X19,X17,X18)|~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.12/0.37  cnf(c_0_25, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk2_0)|k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_26, negated_conjecture, (k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_funct_1(esk3_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.12/0.37  cnf(c_0_27, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.12/0.37  cnf(c_0_28, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.12/0.37  fof(c_0_29, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|k2_relset_1(X13,X14,X15)=k2_relat_1(X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.12/0.37  cnf(c_0_30, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0))!=k2_struct_0(esk1_0)|k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_25, c_0_26])).
% 0.12/0.37  cnf(c_0_31, plain, (k1_relset_1(X1,X2,k2_funct_1(X3))=k1_relat_1(k2_funct_1(X3))|k2_relset_1(X2,X1,X3)!=X1|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v2_funct_1(X3)|~v1_funct_1(X3)), inference(pm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.37  cnf(c_0_32, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.37  cnf(c_0_33, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_30, c_0_26])).
% 0.12/0.37  cnf(c_0_34, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=k1_relat_1(k2_funct_1(esk3_0))|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_31, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.12/0.37  cnf(c_0_35, plain, (k2_relset_1(X1,X2,k2_funct_1(X3))=k2_relat_1(k2_funct_1(X3))|k2_relset_1(X2,X1,X3)!=X1|~v1_funct_2(X3,X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v2_funct_1(X3)|~v1_funct_1(X3)), inference(pm,[status(thm)],[c_0_32, c_0_28])).
% 0.12/0.37  fof(c_0_36, plain, ![X7, X8, X9]:(~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|v1_relat_1(X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.12/0.37  cnf(c_0_37, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k1_relat_1(k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.37  cnf(c_0_38, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))=k2_relat_1(k2_funct_1(esk3_0))|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_35, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.12/0.37  fof(c_0_39, plain, ![X5]:((k2_relat_1(X5)=k1_relat_1(k2_funct_1(X5))|~v2_funct_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5)))&(k1_relat_1(X5)=k2_relat_1(k2_funct_1(X5))|~v2_funct_1(X5)|(~v1_relat_1(X5)|~v1_funct_1(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.12/0.37  cnf(c_0_40, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.12/0.37  fof(c_0_41, plain, ![X20, X21, X22]:((k5_relat_1(X22,k2_funct_1(X22))=k6_partfun1(X20)|X21=k1_xboole_0|(k2_relset_1(X20,X21,X22)!=X21|~v2_funct_1(X22))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))&(k5_relat_1(k2_funct_1(X22),X22)=k6_partfun1(X21)|X21=k1_xboole_0|(k2_relset_1(X20,X21,X22)!=X21|~v2_funct_1(X22))|(~v1_funct_1(X22)|~v1_funct_2(X22,X20,X21)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X20,X21)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_2])])])).
% 0.12/0.37  fof(c_0_42, plain, ![X16]:k6_partfun1(X16)=k6_relat_1(X16), inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).
% 0.12/0.37  cnf(c_0_43, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))!=k2_struct_0(esk1_0)|k1_relat_1(k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.37  cnf(c_0_44, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_45, negated_conjecture, (v1_relat_1(esk3_0)), inference(pm,[status(thm)],[c_0_40, c_0_18])).
% 0.12/0.37  cnf(c_0_46, plain, (k5_relat_1(X1,k2_funct_1(X1))=k6_partfun1(X2)|X3=k1_xboole_0|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.12/0.37  cnf(c_0_47, plain, (k6_partfun1(X1)=k6_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.12/0.37  cnf(c_0_48, negated_conjecture, (k1_relat_1(k2_funct_1(esk3_0))!=k2_struct_0(esk2_0)|k2_struct_0(esk1_0)!=k1_relat_1(esk3_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_43, c_0_44]), c_0_21]), c_0_22]), c_0_45])])).
% 0.12/0.37  cnf(c_0_49, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.37  cnf(c_0_50, negated_conjecture, (k2_relat_1(esk3_0)=k2_struct_0(esk2_0)), inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_32, c_0_18]), c_0_19])).
% 0.12/0.37  fof(c_0_51, plain, ![X23]:(~l1_struct_0(X23)|k2_struct_0(X23)=u1_struct_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.12/0.37  fof(c_0_52, plain, ![X6]:((k1_relat_1(k5_relat_1(X6,k2_funct_1(X6)))=k1_relat_1(X6)|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(k2_relat_1(k5_relat_1(X6,k2_funct_1(X6)))=k1_relat_1(X6)|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_funct_1])])])).
% 0.12/0.37  cnf(c_0_53, plain, (X3=k1_xboole_0|k5_relat_1(X1,k2_funct_1(X1))=k6_relat_1(X2)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v2_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(rw,[status(thm)],[c_0_46, c_0_47])).
% 0.12/0.37  fof(c_0_54, plain, ![X4]:(k1_relat_1(k6_relat_1(X4))=X4&k2_relat_1(k6_relat_1(X4))=X4), inference(variable_rename,[status(thm)],[t71_relat_1])).
% 0.12/0.37  cnf(c_0_55, negated_conjecture, (k2_struct_0(esk1_0)!=k1_relat_1(esk3_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_21]), c_0_22]), c_0_45])])).
% 0.12/0.37  cnf(c_0_56, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.12/0.37  cnf(c_0_57, negated_conjecture, (l1_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_58, plain, (k1_relat_1(k5_relat_1(X1,k2_funct_1(X1)))=k1_relat_1(X1)|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.12/0.37  cnf(c_0_59, negated_conjecture, (k5_relat_1(esk3_0,k2_funct_1(esk3_0))=k6_relat_1(u1_struct_0(esk1_0))|u1_struct_0(esk2_0)=k1_xboole_0|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_53, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.12/0.37  cnf(c_0_60, plain, (k1_relat_1(k6_relat_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.12/0.37  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk1_0)!=k1_relat_1(esk3_0)|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.12/0.37  cnf(c_0_62, negated_conjecture, (u1_struct_0(esk1_0)=k1_relat_1(esk3_0)|u1_struct_0(esk2_0)=k1_xboole_0|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), c_0_21]), c_0_22]), c_0_45])])).
% 0.12/0.37  fof(c_0_63, plain, ![X24]:(v2_struct_0(X24)|~l1_struct_0(X24)|~v1_xboole_0(u1_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.12/0.37  cnf(c_0_64, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|k2_struct_0(esk2_0)!=u1_struct_0(esk2_0)), inference(pm,[status(thm)],[c_0_61, c_0_62])).
% 0.12/0.37  cnf(c_0_65, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_66, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.12/0.37  cnf(c_0_67, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_64, c_0_56]), c_0_65])])).
% 0.12/0.37  cnf(c_0_68, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.37  cnf(c_0_69, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.37  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_65])]), c_0_69]), ['proof']).
% 0.12/0.37  # SZS output end CNFRefutation
% 0.12/0.37  # Proof object total steps             : 71
% 0.12/0.37  # Proof object clause steps            : 43
% 0.12/0.37  # Proof object formula steps           : 28
% 0.12/0.37  # Proof object conjectures             : 29
% 0.12/0.37  # Proof object clause conjectures      : 26
% 0.12/0.37  # Proof object formula conjectures     : 3
% 0.12/0.37  # Proof object initial clauses used    : 23
% 0.12/0.37  # Proof object initial formulas used   : 14
% 0.12/0.37  # Proof object generating inferences   : 19
% 0.12/0.37  # Proof object simplifying inferences  : 44
% 0.12/0.37  # Training examples: 0 positive, 0 negative
% 0.12/0.37  # Parsed axioms                        : 14
% 0.12/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.37  # Initial clauses                      : 28
% 0.12/0.37  # Removed in clause preprocessing      : 1
% 0.12/0.37  # Initial clauses in saturation        : 27
% 0.12/0.37  # Processed clauses                    : 76
% 0.12/0.37  # ...of these trivial                  : 0
% 0.12/0.37  # ...subsumed                          : 8
% 0.12/0.37  # ...remaining for further processing  : 68
% 0.12/0.37  # Other redundant clauses eliminated   : 0
% 0.12/0.37  # Clauses deleted for lack of memory   : 0
% 0.12/0.37  # Backward-subsumed                    : 20
% 0.12/0.37  # Backward-rewritten                   : 18
% 0.12/0.37  # Generated clauses                    : 90
% 0.12/0.37  # ...of the previous two non-trivial   : 105
% 0.12/0.37  # Contextual simplify-reflections      : 0
% 0.12/0.37  # Paramodulations                      : 89
% 0.12/0.37  # Factorizations                       : 1
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
% 0.12/0.37  # Current number of processed clauses  : 30
% 0.12/0.37  #    Positive orientable unit clauses  : 10
% 0.12/0.37  #    Positive unorientable unit clauses: 0
% 0.12/0.37  #    Negative unit clauses             : 1
% 0.12/0.37  #    Non-unit-clauses                  : 19
% 0.12/0.37  # Current number of unprocessed clauses: 39
% 0.12/0.37  # ...number of literals in the above   : 310
% 0.12/0.37  # Current number of archived formulas  : 0
% 0.12/0.37  # Current number of archived clauses   : 39
% 0.12/0.37  # Clause-clause subsumption calls (NU) : 198
% 0.12/0.37  # Rec. Clause-clause subsumption calls : 84
% 0.12/0.37  # Non-unit clause-clause subsumptions  : 28
% 0.12/0.37  # Unit Clause-clause subsumption calls : 0
% 0.12/0.37  # Rewrite failures with RHS unbound    : 0
% 0.12/0.37  # BW rewrite match attempts            : 1
% 0.12/0.37  # BW rewrite match successes           : 1
% 0.12/0.37  # Condensation attempts                : 0
% 0.12/0.37  # Condensation successes               : 0
% 0.12/0.37  # Termbank termtop insertions          : 3256
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.032 s
% 0.12/0.38  # System time              : 0.006 s
% 0.12/0.38  # Total time               : 0.038 s
% 0.12/0.38  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
