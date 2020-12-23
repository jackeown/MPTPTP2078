%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:48 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 370 expanded)
%              Number of clauses        :   51 ( 133 expanded)
%              Number of leaves         :   15 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  315 (2077 expanded)
%              Number of equality atoms :   61 ( 297 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_tops_2,conjecture,(
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
               => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(d4_partfun1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => ( v1_partfun1(X2,X1)
      <=> k1_relat_1(X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(fc5_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(k2_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_tops_2])).

fof(c_0_16,negated_conjecture,
    ( l1_struct_0(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_struct_0(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0)
    & v2_funct_1(esk3_0)
    & ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_17,plain,(
    ! [X14,X15,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))
      | k2_relset_1(X14,X15,X16) = k2_relat_1(X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_18,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = k2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X29] :
      ( ~ l1_struct_0(X29)
      | k2_struct_0(X29) = u1_struct_0(X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_22,negated_conjecture,
    ( k2_relat_1(esk3_0) = k2_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_23,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_24,negated_conjecture,
    ( k2_relset_1(X1,X2,esk3_0) = k2_struct_0(esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_22])).

cnf(c_0_25,negated_conjecture,
    ( l1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(X1,X2,esk3_0) = u1_struct_0(esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])])).

fof(c_0_27,plain,(
    ! [X8,X9,X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | v1_relat_1(X10) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_28,plain,(
    ! [X31,X32,X33] :
      ( ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,X31,X32)
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k2_relset_1(X31,X32,X33) != X32
      | ~ v2_funct_1(X33)
      | k2_tops_2(X31,X32,X33) = k2_funct_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_29,negated_conjecture,
    ( k2_struct_0(esk2_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_26]),c_0_20])])).

fof(c_0_30,plain,(
    ! [X5] :
      ( ( v1_relat_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v2_funct_1(X5) )
      & ( v1_funct_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v2_funct_1(X5) )
      & ( v2_funct_1(k2_funct_1(X5))
        | ~ v1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v2_funct_1(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_31,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_32,plain,(
    ! [X26,X27,X28] :
      ( ( v1_funct_1(k2_funct_1(X28))
        | ~ v2_funct_1(X28)
        | k2_relset_1(X26,X27,X28) != X27
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( v1_funct_2(k2_funct_1(X28),X27,X26)
        | ~ v2_funct_1(X28)
        | k2_relset_1(X26,X27,X28) != X27
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) )
      & ( m1_subset_1(k2_funct_1(X28),k1_zfmisc_1(k2_zfmisc_1(X27,X26)))
        | ~ v2_funct_1(X28)
        | k2_relset_1(X26,X27,X28) != X27
        | ~ v1_funct_1(X28)
        | ~ v1_funct_2(X28,X26,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_33,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_18,c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_20])).

cnf(c_0_41,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_20]),c_0_37]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_37]),c_0_38])])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_35]),c_0_36]),c_0_20]),c_0_37]),c_0_38])])).

fof(c_0_45,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | ~ v1_funct_1(X7)
      | ~ v2_funct_1(X7)
      | k2_funct_1(k2_funct_1(X7)) = X7 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_46,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_43])]),c_0_44])])).

cnf(c_0_47,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_48,plain,(
    ! [X19,X20,X21,X22] :
      ( ( ~ r2_funct_2(X19,X20,X21,X22)
        | X21 = X22
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) )
      & ( X21 != X22
        | r2_funct_2(X19,X20,X21,X22)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,X19,X20)
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
        | ~ v1_funct_1(X22)
        | ~ v1_funct_2(X22,X19,X20)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_49,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_37]),c_0_38]),c_0_40])])).

cnf(c_0_50,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_51,plain,(
    ! [X11,X12,X13] :
      ( ( v4_relat_1(X13,X11)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( v5_relat_1(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_52,plain,(
    ! [X23,X24,X25] :
      ( ( X24 = k1_xboole_0
        | v1_partfun1(X25,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) )
      & ( X23 != k1_xboole_0
        | v1_partfun1(X25,X23)
        | ~ v1_funct_1(X25)
        | ~ v1_funct_2(X25,X23,X24)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))
        | ~ v1_funct_1(X25)
        | ~ m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_54,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_50])).

fof(c_0_55,plain,(
    ! [X17,X18] :
      ( ( ~ v1_partfun1(X18,X17)
        | k1_relat_1(X18) = X17
        | ~ v1_relat_1(X18)
        | ~ v4_relat_1(X18,X17) )
      & ( k1_relat_1(X18) != X17
        | v1_partfun1(X18,X17)
        | ~ v1_relat_1(X18)
        | ~ v4_relat_1(X18,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).

cnf(c_0_56,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

fof(c_0_58,plain,(
    ! [X30] :
      ( v2_struct_0(X30)
      | ~ l1_struct_0(X30)
      | ~ v1_xboole_0(k2_struct_0(X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).

cnf(c_0_59,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_36]),c_0_20]),c_0_38])])).

cnf(c_0_60,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_61,plain,(
    ! [X6] :
      ( ( k2_relat_1(X6) = k1_relat_1(k2_funct_1(X6))
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) )
      & ( k1_relat_1(X6) = k2_relat_1(k2_funct_1(X6))
        | ~ v2_funct_1(X6)
        | ~ v1_relat_1(X6)
        | ~ v1_funct_1(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_62,plain,
    ( k1_relat_1(X1) = X2
    | ~ v1_partfun1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v4_relat_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_20])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | v1_partfun1(X2,X3)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(cn,[status(thm)],[c_0_57])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(k2_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_35]),c_0_36]),c_0_20]),c_0_37]),c_0_38])])).

cnf(c_0_68,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | ~ v1_partfun1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_40])])).

cnf(c_0_70,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_partfun1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_20]),c_0_36]),c_0_38])])).

cnf(c_0_71,negated_conjecture,
    ( ~ m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(k2_relset_1(X1,X2,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_24]),c_0_25])]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( k1_relat_1(esk3_0) != u1_struct_0(esk1_0)
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_37]),c_0_38]),c_0_40])])).

cnf(c_0_73,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ v1_xboole_0(k2_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_18]),c_0_20])])).

cnf(c_0_75,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v2_funct_1(k2_funct_1(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_23]),c_0_25])])).

cnf(c_0_78,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_37]),c_0_38]),c_0_40])])).

cnf(c_0_79,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_78]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.029 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t64_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 0.20/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.39  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 0.20/0.39  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.20/0.39  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.20/0.39  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 0.20/0.39  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.20/0.39  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.39  fof(t132_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0&X1!=k1_xboole_0)|v1_partfun1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 0.20/0.39  fof(d4_partfun1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>(v1_partfun1(X2,X1)<=>k1_relat_1(X2)=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 0.20/0.39  fof(fc5_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(k2_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 0.20/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.20/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.39  fof(c_0_15, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3)))))), inference(assume_negation,[status(cth)],[t64_tops_2])).
% 0.20/0.39  fof(c_0_16, negated_conjecture, (l1_struct_0(esk1_0)&((~v2_struct_0(esk2_0)&l1_struct_0(esk2_0))&(((v1_funct_1(esk3_0)&v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&((k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)&v2_funct_1(esk3_0))&~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.39  fof(c_0_17, plain, ![X14, X15, X16]:(~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15)))|k2_relset_1(X14,X15,X16)=k2_relat_1(X16)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=k2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_19, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  fof(c_0_21, plain, ![X29]:(~l1_struct_0(X29)|k2_struct_0(X29)=u1_struct_0(X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (k2_relat_1(esk3_0)=k2_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.20/0.39  cnf(c_0_23, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k2_relset_1(X1,X2,esk3_0)=k2_struct_0(esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_19, c_0_22])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (l1_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (k2_relset_1(X1,X2,esk3_0)=u1_struct_0(esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])])).
% 0.20/0.39  fof(c_0_27, plain, ![X8, X9, X10]:(~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))|v1_relat_1(X10)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.39  fof(c_0_28, plain, ![X31, X32, X33]:(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|(k2_relset_1(X31,X32,X33)!=X32|~v2_funct_1(X33)|k2_tops_2(X31,X32,X33)=k2_funct_1(X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k2_struct_0(esk2_0)=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_26]), c_0_20])])).
% 0.20/0.39  fof(c_0_30, plain, ![X5]:(((v1_relat_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)|~v2_funct_1(X5)))&(v1_funct_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)|~v2_funct_1(X5))))&(v2_funct_1(k2_funct_1(X5))|(~v1_relat_1(X5)|~v1_funct_1(X5)|~v2_funct_1(X5)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.20/0.39  cnf(c_0_31, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  fof(c_0_32, plain, ![X26, X27, X28]:(((v1_funct_1(k2_funct_1(X28))|(~v2_funct_1(X28)|k2_relset_1(X26,X27,X28)!=X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))&(v1_funct_2(k2_funct_1(X28),X27,X26)|(~v2_funct_1(X28)|k2_relset_1(X26,X27,X28)!=X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27))))))&(m1_subset_1(k2_funct_1(X28),k1_zfmisc_1(k2_zfmisc_1(X27,X26)))|(~v2_funct_1(X28)|k2_relset_1(X26,X27,X28)!=X27)|(~v1_funct_1(X28)|~v1_funct_2(X28,X26,X27)|~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tops_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_34, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0)=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_18, c_0_29])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (v2_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (v1_funct_1(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_39, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_20])).
% 0.20/0.39  cnf(c_0_41, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0)),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_20]), c_0_37]), c_0_38])])).
% 0.20/0.39  cnf(c_0_43, negated_conjecture, (v1_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_37]), c_0_38])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_35]), c_0_36]), c_0_20]), c_0_37]), c_0_38])])).
% 0.20/0.39  fof(c_0_45, plain, ![X7]:(~v1_relat_1(X7)|~v1_funct_1(X7)|(~v2_funct_1(X7)|k2_funct_1(k2_funct_1(X7))=X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),k2_funct_1(k2_funct_1(esk3_0)),esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_34]), c_0_43])]), c_0_44])])).
% 0.20/0.39  cnf(c_0_47, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.20/0.39  fof(c_0_48, plain, ![X19, X20, X21, X22]:((~r2_funct_2(X19,X20,X21,X22)|X21=X22|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))&(X21!=X22|r2_funct_2(X19,X20,X21,X22)|(~v1_funct_1(X21)|~v1_funct_2(X21,X19,X20)|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|~v1_funct_1(X22)|~v1_funct_2(X22,X19,X20)|~m1_subset_1(X22,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_37]), c_0_38]), c_0_40])])).
% 0.20/0.39  cnf(c_0_50, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  fof(c_0_51, plain, ![X11, X12, X13]:((v4_relat_1(X13,X11)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))&(v5_relat_1(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.39  fof(c_0_52, plain, ![X23, X24, X25]:((X24=k1_xboole_0|v1_partfun1(X25,X23)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))&(X23!=k1_xboole_0|v1_partfun1(X25,X23)|(~v1_funct_1(X25)|~v1_funct_2(X25,X23,X24)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24))))|(~v1_funct_1(X25)|~m1_subset_1(X25,k1_zfmisc_1(k2_zfmisc_1(X23,X24)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t132_funct_2])])])).
% 0.20/0.39  cnf(c_0_53, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0,esk3_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v2_funct_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_49, c_0_19])).
% 0.20/0.39  cnf(c_0_54, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_50])).
% 0.20/0.39  fof(c_0_55, plain, ![X17, X18]:((~v1_partfun1(X18,X17)|k1_relat_1(X18)=X17|(~v1_relat_1(X18)|~v4_relat_1(X18,X17)))&(k1_relat_1(X18)!=X17|v1_partfun1(X18,X17)|(~v1_relat_1(X18)|~v4_relat_1(X18,X17)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_partfun1])])])).
% 0.20/0.39  cnf(c_0_56, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_57, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.39  fof(c_0_58, plain, ![X30]:(v2_struct_0(X30)|~l1_struct_0(X30)|~v1_xboole_0(k2_struct_0(X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc5_struct_0])])])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))|~v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_36]), c_0_20]), c_0_38])])).
% 0.20/0.39  cnf(c_0_60, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.39  fof(c_0_61, plain, ![X6]:((k2_relat_1(X6)=k1_relat_1(k2_funct_1(X6))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))&(k1_relat_1(X6)=k2_relat_1(k2_funct_1(X6))|~v2_funct_1(X6)|(~v1_relat_1(X6)|~v1_funct_1(X6)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.20/0.39  cnf(c_0_62, plain, (k1_relat_1(X1)=X2|~v1_partfun1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (v4_relat_1(esk3_0,u1_struct_0(esk1_0))), inference(spm,[status(thm)],[c_0_56, c_0_20])).
% 0.20/0.39  cnf(c_0_64, plain, (X1=k1_xboole_0|v1_partfun1(X2,X3)|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(cn,[status(thm)],[c_0_57])).
% 0.20/0.39  cnf(c_0_65, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(k2_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (k2_relat_1(k2_funct_1(esk3_0))!=u1_struct_0(esk1_0)|~v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_35]), c_0_36]), c_0_20]), c_0_37]), c_0_38])])).
% 0.20/0.39  cnf(c_0_68, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|~v1_partfun1(esk3_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_40])])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_partfun1(esk3_0,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_20]), c_0_36]), c_0_38])])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, (~m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(k2_relset_1(X1,X2,esk3_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_24]), c_0_25])]), c_0_66])).
% 0.20/0.39  cnf(c_0_72, negated_conjecture, (k1_relat_1(esk3_0)!=u1_struct_0(esk1_0)|~v2_funct_1(k2_funct_1(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_37]), c_0_38]), c_0_40])])).
% 0.20/0.39  cnf(c_0_73, negated_conjecture, (k1_relat_1(esk3_0)=u1_struct_0(esk1_0)|u1_struct_0(esk2_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.20/0.39  cnf(c_0_74, negated_conjecture, (~v1_xboole_0(k2_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_18]), c_0_20])])).
% 0.20/0.39  cnf(c_0_75, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|~v2_funct_1(k2_funct_1(esk3_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.39  cnf(c_0_76, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_77, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_23]), c_0_25])])).
% 0.20/0.39  cnf(c_0_78, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_37]), c_0_38]), c_0_40])])).
% 0.20/0.39  cnf(c_0_79, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.39  cnf(c_0_80, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77, c_0_78]), c_0_79])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 81
% 0.20/0.39  # Proof object clause steps            : 51
% 0.20/0.39  # Proof object formula steps           : 30
% 0.20/0.39  # Proof object conjectures             : 36
% 0.20/0.39  # Proof object clause conjectures      : 33
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 24
% 0.20/0.39  # Proof object initial formulas used   : 15
% 0.20/0.39  # Proof object generating inferences   : 23
% 0.20/0.39  # Proof object simplifying inferences  : 64
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 15
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 32
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 32
% 0.20/0.39  # Processed clauses                    : 103
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 8
% 0.20/0.39  # ...remaining for further processing  : 94
% 0.20/0.39  # Other redundant clauses eliminated   : 6
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 2
% 0.20/0.39  # Backward-rewritten                   : 20
% 0.20/0.39  # Generated clauses                    : 68
% 0.20/0.39  # ...of the previous two non-trivial   : 66
% 0.20/0.39  # Contextual simplify-reflections      : 0
% 0.20/0.39  # Paramodulations                      : 62
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 6
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 37
% 0.20/0.39  #    Positive orientable unit clauses  : 9
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 27
% 0.20/0.39  # Current number of unprocessed clauses: 20
% 0.20/0.39  # ...number of literals in the above   : 107
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 54
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 469
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 63
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 4
% 0.20/0.39  # Unit Clause-clause subsumption calls : 5
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 2
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 4241
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.032 s
% 0.20/0.39  # System time              : 0.007 s
% 0.20/0.39  # Total time               : 0.038 s
% 0.20/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
