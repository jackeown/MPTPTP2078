%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (244228 expanded)
%              Number of clauses        :  104 (83949 expanded)
%              Number of leaves         :   18 (59881 expanded)
%              Depth                    :   31
%              Number of atoms          :  490 (1425513 expanded)
%              Number of equality atoms :  121 (220843 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t65_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => k2_funct_1(k2_funct_1(X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(reflexivity_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r2_funct_2(X1,X2,X3,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(rc1_funct_2,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_relat_1(X3)
      & v4_relat_1(X3,X1)
      & v5_relat_1(X3,X2)
      & v1_funct_1(X3)
      & v1_funct_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(dt_k2_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_tops_2(X1,X2,X3))
        & v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
        & m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(t67_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => k1_relset_1(X1,X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(c_0_18,negated_conjecture,(
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

fof(c_0_19,negated_conjecture,
    ( l1_struct_0(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & l1_struct_0(esk3_0)
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0)
    & v2_funct_1(esk4_0)
    & ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).

fof(c_0_20,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | k2_relset_1(X19,X20,X21) = k2_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_21,plain,(
    ! [X39] :
      ( ~ l1_struct_0(X39)
      | k2_struct_0(X39) = u1_struct_0(X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_22,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = k2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k2_struct_0(esk3_0) = k2_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( l1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_funct_1(X42)
      | ~ v1_funct_2(X42,X40,X41)
      | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))
      | k2_relset_1(X40,X41,X42) != X41
      | ~ v2_funct_1(X42)
      | k2_tops_2(X40,X41,X42) = k2_funct_1(X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_29,negated_conjecture,
    ( k2_relat_1(esk4_0) = u1_struct_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

fof(c_0_30,plain,(
    ! [X32,X33,X34] :
      ( ( v1_funct_1(k2_funct_1(X34))
        | ~ v2_funct_1(X34)
        | k2_relset_1(X32,X33,X34) != X33
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( v1_funct_2(k2_funct_1(X34),X33,X32)
        | ~ v2_funct_1(X34)
        | k2_relset_1(X32,X33,X34) != X33
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) )
      & ( m1_subset_1(k2_funct_1(X34),k1_zfmisc_1(k2_zfmisc_1(X33,X32)))
        | ~ v2_funct_1(X34)
        | k2_relset_1(X32,X33,X34) != X33
        | ~ v1_funct_1(X34)
        | ~ v1_funct_2(X34,X32,X33)
        | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_26]),c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_37,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_38,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_24])])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_24])])).

fof(c_0_41,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9)
      | k2_funct_1(k2_funct_1(X9)) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).

cnf(c_0_42,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_43,plain,(
    ! [X8] :
      ( ( k2_relat_1(X8) = k1_relat_1(k2_funct_1(X8))
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) )
      & ( k1_relat_1(X8) = k2_relat_1(k2_funct_1(X8))
        | ~ v2_funct_1(X8)
        | ~ v1_relat_1(X8)
        | ~ v1_funct_1(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_40])])).

cnf(c_0_45,plain,
    ( k2_funct_1(k2_funct_1(X1)) = X1
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_24])).

cnf(c_0_47,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_48,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v1_funct_1(X30)
      | ~ v1_funct_2(X30,X28,X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X28,X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | r2_funct_2(X28,X29,X30,X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).

cnf(c_0_49,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_35]),c_0_36]),c_0_46])])).

cnf(c_0_50,plain,
    ( k2_relset_1(X1,X2,k2_funct_1(X3)) = k1_relat_1(X3)
    | ~ v2_funct_1(X3)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X3)
    | ~ m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_23])).

cnf(c_0_51,plain,
    ( r2_funct_2(X2,X3,X1,X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0)
    | ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35]),c_0_36]),c_0_46])])).

cnf(c_0_53,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,X1)
    | ~ v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_24]),c_0_34]),c_0_36])])).

fof(c_0_54,plain,(
    ! [X22,X23,X24] :
      ( ( ~ v1_funct_2(X24,X22,X23)
        | X22 = k1_relset_1(X22,X23,X24)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X22 != k1_relset_1(X22,X23,X24)
        | v1_funct_2(X24,X22,X23)
        | X23 = k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ v1_funct_2(X24,X22,X23)
        | X22 = k1_relset_1(X22,X23,X24)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X22 != k1_relset_1(X22,X23,X24)
        | v1_funct_2(X24,X22,X23)
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( ~ v1_funct_2(X24,X22,X23)
        | X24 = k1_xboole_0
        | X22 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) )
      & ( X24 != k1_xboole_0
        | v1_funct_2(X24,X22,X23)
        | X22 = k1_xboole_0
        | X23 != k1_xboole_0
        | ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_55,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0)
    | ~ v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_34]),c_0_36]),c_0_24])])).

cnf(c_0_56,plain,
    ( v1_funct_2(k2_funct_1(X1),X2,X3)
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_57,plain,(
    ! [X35,X36] :
      ( ( v1_funct_1(X36)
        | ~ r1_tarski(k2_relat_1(X36),X35)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( v1_funct_2(X36,k1_relat_1(X36),X35)
        | ~ r1_tarski(k2_relat_1(X36),X35)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) )
      & ( m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X36),X35)))
        | ~ r1_tarski(k2_relat_1(X36),X35)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_58,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | m1_subset_1(k2_relset_1(X13,X14,X15),k1_zfmisc_1(X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_59,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | k1_relset_1(X16,X17,X18) = k1_relat_1(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_60,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_funct_1(esk4_0))
    | ~ m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_24])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | k2_relset_1(X3,X2,X1) != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_63,plain,(
    ! [X7] :
      ( ( v1_relat_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X7) )
      & ( v1_funct_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X7) )
      & ( v2_funct_1(k2_funct_1(X7))
        | ~ v1_relat_1(X7)
        | ~ v1_funct_1(X7)
        | ~ v2_funct_1(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_65,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | m1_subset_1(X5,k1_zfmisc_1(X6)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_66,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_67,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_68,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_24]),c_0_34])])).

cnf(c_0_70,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0)
    | ~ v2_funct_1(k2_funct_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_33]),c_0_34]),c_0_35]),c_0_36]),c_0_24])])).

cnf(c_0_71,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),X1)))
    | ~ r1_tarski(u1_struct_0(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_29]),c_0_36]),c_0_46])])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relat_1(esk4_0),X1)
    | ~ r1_tarski(u1_struct_0(esk3_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_29]),c_0_36]),c_0_46])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_22]),c_0_24])])).

cnf(c_0_77,negated_conjecture,
    ( k1_relat_1(esk4_0) = u1_struct_0(esk2_0)
    | u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_24])])).

cnf(c_0_78,negated_conjecture,
    ( k1_relat_1(esk4_0) != u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_35]),c_0_36]),c_0_46])])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),X1)))
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relat_1(esk4_0),X1)
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_25]),c_0_27])])).

cnf(c_0_83,negated_conjecture,
    ( u1_struct_0(esk3_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_77,c_0_78])).

fof(c_0_84,plain,(
    ! [X25,X26] :
      ( m1_subset_1(esk1_2(X25,X26),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      & v1_relat_1(esk1_2(X25,X26))
      & v4_relat_1(esk1_2(X25,X26),X25)
      & v5_relat_1(esk1_2(X25,X26),X26)
      & v1_funct_1(esk1_2(X25,X26))
      & v1_funct_2(esk1_2(X25,X26),X25,X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).

cnf(c_0_85,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_24,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_83])).

cnf(c_0_89,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,plain,
    ( v1_funct_2(esk1_2(X1,X2),X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

fof(c_0_91,plain,(
    ! [X43,X44,X45] :
      ( ( v1_funct_1(k2_tops_2(X43,X44,X45))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( v1_funct_2(k2_tops_2(X43,X44,X45),X44,X43)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( m1_subset_1(k2_tops_2(X43,X44,X45),k1_zfmisc_1(k2_zfmisc_1(X44,X43)))
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X43,X44)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_83]),c_0_86])])).

cnf(c_0_93,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_87]),c_0_88])])).

cnf(c_0_94,plain,
    ( v1_funct_1(esk1_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_95,plain,
    ( esk1_2(X1,k1_xboole_0) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_89]),c_0_90])])).

cnf(c_0_96,plain,
    ( m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_97,plain,
    ( v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_91])).

cnf(c_0_98,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_92]),c_0_93])).

cnf(c_0_99,plain,
    ( X1 = k1_xboole_0
    | v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_100,plain,
    ( k1_relset_1(X1,X2,k2_tops_2(X2,X1,X3)) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X3,X2,X1)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_96]),c_0_97])).

cnf(c_0_101,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_87,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_88,c_0_98])).

cnf(c_0_103,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_99])).

cnf(c_0_104,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),k1_xboole_0,esk4_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_83]),c_0_83])).

cnf(c_0_105,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_103])])).

cnf(c_0_106,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk2_0),k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_104,c_0_98])).

cnf(c_0_107,negated_conjecture,
    ( v2_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_35,c_0_98])).

cnf(c_0_108,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,u1_struct_0(esk2_0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_32]),c_0_106]),c_0_102]),c_0_107]),c_0_103]),c_0_101])])).

cnf(c_0_109,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_108])).

cnf(c_0_110,plain,
    ( v1_relat_1(esk1_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_111,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_74])).

cnf(c_0_112,negated_conjecture,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_62]),c_0_106]),c_0_102]),c_0_107]),c_0_103]),c_0_101])])).

cnf(c_0_113,negated_conjecture,
    ( v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_40,c_0_98])).

cnf(c_0_114,plain,
    ( X1 = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_95])).

cnf(c_0_115,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_23])).

cnf(c_0_116,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_117,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_relat_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])])).

cnf(c_0_118,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_119,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_110,c_0_114])).

cnf(c_0_120,plain,
    ( m1_subset_1(k2_relat_1(k2_funct_1(X1)),k1_zfmisc_1(X2))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v1_funct_2(X1,X2,X3)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_115,c_0_62])).

cnf(c_0_121,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_116])).

cnf(c_0_122,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_relat_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_118]),c_0_107]),c_0_103]),c_0_119])])).

cnf(c_0_123,negated_conjecture,
    ( m1_subset_1(k2_relat_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_101]),c_0_106]),c_0_102]),c_0_107]),c_0_103])])).

cnf(c_0_124,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_121,c_0_108])).

cnf(c_0_125,plain,
    ( k2_tops_2(k1_xboole_0,X1,X2) = k1_xboole_0
    | X1 = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_96]),c_0_97])).

cnf(c_0_126,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_122,c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_62]),c_0_106]),c_0_102]),c_0_107]),c_0_103]),c_0_101])])).

cnf(c_0_128,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),k1_xboole_0,k2_tops_2(k1_xboole_0,u1_struct_0(esk2_0),k2_funct_1(k1_xboole_0)),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_83]),c_0_83]),c_0_98]),c_0_98])).

cnf(c_0_129,negated_conjecture,
    ( k2_tops_2(k1_xboole_0,u1_struct_0(esk2_0),k2_funct_1(k1_xboole_0)) = k1_xboole_0
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_126]),c_0_113])]),c_0_127])).

fof(c_0_130,plain,(
    ! [X37,X38] :
      ( ~ v1_funct_1(X38)
      | ~ v1_funct_2(X38,X37,X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X37)))
      | k1_relset_1(X37,X37,X38) = X37 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).

cnf(c_0_131,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ r2_funct_2(u1_struct_0(esk2_0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_132,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_89]),c_0_90]),c_0_94])])).

cnf(c_0_133,plain,
    ( k1_relset_1(X2,X2,X1) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_130])).

cnf(c_0_134,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_102]),c_0_103]),c_0_101])])).

cnf(c_0_135,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != u1_struct_0(esk2_0) ),
    inference(rw,[status(thm)],[c_0_78,c_0_98])).

cnf(c_0_136,plain,
    ( X1 = k1_relat_1(X2)
    | ~ v1_funct_2(X2,X1,X1)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_133])).

cnf(c_0_137,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_101,c_0_134])).

cnf(c_0_138,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_102,c_0_134])).

cnf(c_0_139,negated_conjecture,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_135,c_0_134])).

cnf(c_0_140,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_138]),c_0_103])]),c_0_139]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.44  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.44  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.44  #
% 0.19/0.44  # Preprocessing time       : 0.029 s
% 0.19/0.44  # Presaturation interreduction done
% 0.19/0.44  
% 0.19/0.44  # Proof found!
% 0.19/0.44  # SZS status Theorem
% 0.19/0.44  # SZS output start CNFRefutation
% 0.19/0.44  fof(t64_tops_2, conjecture, ![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tops_2)).
% 0.19/0.44  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.44  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.44  fof(d4_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((k2_relset_1(X1,X2,X3)=X2&v2_funct_1(X3))=>k2_tops_2(X1,X2,X3)=k2_funct_1(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tops_2)).
% 0.19/0.44  fof(t31_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.19/0.44  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.44  fof(t65_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>k2_funct_1(k2_funct_1(X1))=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 0.19/0.44  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.19/0.44  fof(reflexivity_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r2_funct_2(X1,X2,X3,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 0.19/0.44  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.44  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 0.19/0.44  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.19/0.44  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.44  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.19/0.44  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.44  fof(rc1_funct_2, axiom, ![X1, X2]:?[X3]:(((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&v1_relat_1(X3))&v4_relat_1(X3,X1))&v5_relat_1(X3,X2))&v1_funct_1(X3))&v1_funct_2(X3,X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 0.19/0.44  fof(dt_k2_tops_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v1_funct_1(k2_tops_2(X1,X2,X3))&v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1))&m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_2)).
% 0.19/0.44  fof(t67_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>k1_relset_1(X1,X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 0.19/0.44  fof(c_0_18, negated_conjecture, ~(![X1]:(l1_struct_0(X1)=>![X2]:((~(v2_struct_0(X2))&l1_struct_0(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>((k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3)=k2_struct_0(X2)&v2_funct_1(X3))=>r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k2_tops_2(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)),X3)))))), inference(assume_negation,[status(cth)],[t64_tops_2])).
% 0.19/0.44  fof(c_0_19, negated_conjecture, (l1_struct_0(esk2_0)&((~v2_struct_0(esk3_0)&l1_struct_0(esk3_0))&(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))))&((k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)&v2_funct_1(esk4_0))&~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_18])])])])).
% 0.19/0.44  fof(c_0_20, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|k2_relset_1(X19,X20,X21)=k2_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.44  fof(c_0_21, plain, ![X39]:(~l1_struct_0(X39)|k2_struct_0(X39)=u1_struct_0(X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.44  cnf(c_0_22, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=k2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_23, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.44  cnf(c_0_24, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_25, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.44  cnf(c_0_26, negated_conjecture, (k2_struct_0(esk3_0)=k2_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.44  cnf(c_0_27, negated_conjecture, (l1_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  fof(c_0_28, plain, ![X40, X41, X42]:(~v1_funct_1(X42)|~v1_funct_2(X42,X40,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41)))|(k2_relset_1(X40,X41,X42)!=X41|~v2_funct_1(X42)|k2_tops_2(X40,X41,X42)=k2_funct_1(X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).
% 0.19/0.44  cnf(c_0_29, negated_conjecture, (k2_relat_1(esk4_0)=u1_struct_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27])])).
% 0.19/0.44  fof(c_0_30, plain, ![X32, X33, X34]:(((v1_funct_1(k2_funct_1(X34))|(~v2_funct_1(X34)|k2_relset_1(X32,X33,X34)!=X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))&(v1_funct_2(k2_funct_1(X34),X33,X32)|(~v2_funct_1(X34)|k2_relset_1(X32,X33,X34)!=X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33))))))&(m1_subset_1(k2_funct_1(X34),k1_zfmisc_1(k2_zfmisc_1(X33,X32)))|(~v2_funct_1(X34)|k2_relset_1(X32,X33,X34)!=X33)|(~v1_funct_1(X34)|~v1_funct_2(X34,X32,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_funct_2])])])).
% 0.19/0.44  cnf(c_0_31, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_32, plain, (k2_tops_2(X2,X3,X1)=k2_funct_1(X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|k2_relset_1(X2,X3,X1)!=X3|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.44  cnf(c_0_33, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk3_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_26]), c_0_29])).
% 0.19/0.44  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_35, negated_conjecture, (v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.44  cnf(c_0_37, plain, (v1_funct_1(k2_funct_1(X1))|~v2_funct_1(X1)|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  fof(c_0_38, plain, ![X10, X11, X12]:(~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))|v1_relat_1(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.44  cnf(c_0_39, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_tops_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0)),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_24])])).
% 0.19/0.44  cnf(c_0_40, negated_conjecture, (v1_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_24])])).
% 0.19/0.44  fof(c_0_41, plain, ![X9]:(~v1_relat_1(X9)|~v1_funct_1(X9)|(~v2_funct_1(X9)|k2_funct_1(k2_funct_1(X9))=X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_funct_1])])).
% 0.19/0.44  cnf(c_0_42, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.44  fof(c_0_43, plain, ![X8]:((k2_relat_1(X8)=k1_relat_1(k2_funct_1(X8))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))&(k1_relat_1(X8)=k2_relat_1(k2_funct_1(X8))|~v2_funct_1(X8)|(~v1_relat_1(X8)|~v1_funct_1(X8)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.19/0.44  cnf(c_0_44, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),k2_funct_1(k2_funct_1(esk4_0)),esk4_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_32]), c_0_40])])).
% 0.19/0.44  cnf(c_0_45, plain, (k2_funct_1(k2_funct_1(X1))=X1|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.44  cnf(c_0_46, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_42, c_0_24])).
% 0.19/0.44  cnf(c_0_47, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.44  fof(c_0_48, plain, ![X28, X29, X30, X31]:(~v1_funct_1(X30)|~v1_funct_2(X30,X28,X29)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|r2_funct_2(X28,X29,X30,X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[reflexivity_r2_funct_2])])).
% 0.19/0.44  cnf(c_0_49, negated_conjecture, (k2_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_funct_1(esk4_0))!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_35]), c_0_36]), c_0_46])])).
% 0.19/0.44  cnf(c_0_50, plain, (k2_relset_1(X1,X2,k2_funct_1(X3))=k1_relat_1(X3)|~v2_funct_1(X3)|~v1_funct_1(X3)|~v1_relat_1(X3)|~m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_47, c_0_23])).
% 0.19/0.44  cnf(c_0_51, plain, (r2_funct_2(X2,X3,X1,X1)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_funct_1(X4)|~v1_funct_2(X4,X2,X3)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.44  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)|~r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk4_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35]), c_0_36]), c_0_46])])).
% 0.19/0.44  cnf(c_0_53, negated_conjecture, (r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk3_0),X1,X1)|~v1_funct_2(X1,u1_struct_0(esk2_0),u1_struct_0(esk3_0))|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_24]), c_0_34]), c_0_36])])).
% 0.19/0.44  fof(c_0_54, plain, ![X22, X23, X24]:((((~v1_funct_2(X24,X22,X23)|X22=k1_relset_1(X22,X23,X24)|X23=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X22!=k1_relset_1(X22,X23,X24)|v1_funct_2(X24,X22,X23)|X23=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))&((~v1_funct_2(X24,X22,X23)|X22=k1_relset_1(X22,X23,X24)|X22!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X22!=k1_relset_1(X22,X23,X24)|v1_funct_2(X24,X22,X23)|X22!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))))&((~v1_funct_2(X24,X22,X23)|X24=k1_xboole_0|X22=k1_xboole_0|X23!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23))))&(X24!=k1_xboole_0|v1_funct_2(X24,X22,X23)|X22=k1_xboole_0|X23!=k1_xboole_0|~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.44  cnf(c_0_55, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)|~v1_funct_2(k2_funct_1(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0))|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_34]), c_0_36]), c_0_24])])).
% 0.19/0.44  cnf(c_0_56, plain, (v1_funct_2(k2_funct_1(X1),X2,X3)|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  fof(c_0_57, plain, ![X35, X36]:(((v1_funct_1(X36)|~r1_tarski(k2_relat_1(X36),X35)|(~v1_relat_1(X36)|~v1_funct_1(X36)))&(v1_funct_2(X36,k1_relat_1(X36),X35)|~r1_tarski(k2_relat_1(X36),X35)|(~v1_relat_1(X36)|~v1_funct_1(X36))))&(m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X36),X35)))|~r1_tarski(k2_relat_1(X36),X35)|(~v1_relat_1(X36)|~v1_funct_1(X36)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 0.19/0.44  fof(c_0_58, plain, ![X13, X14, X15]:(~m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))|m1_subset_1(k2_relset_1(X13,X14,X15),k1_zfmisc_1(X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.19/0.44  fof(c_0_59, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))|k1_relset_1(X16,X17,X18)=k1_relat_1(X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.44  cnf(c_0_60, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.44  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)|~v2_funct_1(k2_funct_1(esk4_0))|~m1_subset_1(k2_funct_1(esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_24])])).
% 0.19/0.44  cnf(c_0_62, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|k2_relset_1(X3,X2,X1)!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.44  fof(c_0_63, plain, ![X7]:(((v1_relat_1(k2_funct_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)|~v2_funct_1(X7)))&(v1_funct_1(k2_funct_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)|~v2_funct_1(X7))))&(v2_funct_1(k2_funct_1(X7))|(~v1_relat_1(X7)|~v1_funct_1(X7)|~v2_funct_1(X7)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.19/0.44  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.44  fof(c_0_65, plain, ![X5, X6]:((~m1_subset_1(X5,k1_zfmisc_1(X6))|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|m1_subset_1(X5,k1_zfmisc_1(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.44  cnf(c_0_66, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.19/0.44  cnf(c_0_67, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.19/0.44  cnf(c_0_68, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.19/0.44  cnf(c_0_69, negated_conjecture, (k1_relset_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_24]), c_0_34])])).
% 0.19/0.44  cnf(c_0_70, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)|~v2_funct_1(k2_funct_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_33]), c_0_34]), c_0_35]), c_0_36]), c_0_24])])).
% 0.19/0.44  cnf(c_0_71, plain, (v2_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.44  cnf(c_0_72, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.44  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),X1)))|~r1_tarski(u1_struct_0(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_29]), c_0_36]), c_0_46])])).
% 0.19/0.44  cnf(c_0_74, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.19/0.44  cnf(c_0_75, negated_conjecture, (v1_funct_2(esk4_0,k1_relat_1(esk4_0),X1)|~r1_tarski(u1_struct_0(esk3_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_29]), c_0_36]), c_0_46])])).
% 0.19/0.44  cnf(c_0_76, negated_conjecture, (m1_subset_1(k2_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_22]), c_0_24])])).
% 0.19/0.44  cnf(c_0_77, negated_conjecture, (k1_relat_1(esk4_0)=u1_struct_0(esk2_0)|u1_struct_0(esk3_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_24])])).
% 0.19/0.44  cnf(c_0_78, negated_conjecture, (k1_relat_1(esk4_0)!=u1_struct_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_35]), c_0_36]), c_0_46])])).
% 0.19/0.44  cnf(c_0_79, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_72])).
% 0.19/0.44  cnf(c_0_80, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),X1)))|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.44  cnf(c_0_81, negated_conjecture, (v1_funct_2(esk4_0,k1_relat_1(esk4_0),X1)|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_75, c_0_74])).
% 0.19/0.44  cnf(c_0_82, negated_conjecture, (m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_25]), c_0_27])])).
% 0.19/0.44  cnf(c_0_83, negated_conjecture, (u1_struct_0(esk3_0)=k1_xboole_0), inference(sr,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.44  fof(c_0_84, plain, ![X25, X26]:(((((m1_subset_1(esk1_2(X25,X26),k1_zfmisc_1(k2_zfmisc_1(X25,X26)))&v1_relat_1(esk1_2(X25,X26)))&v4_relat_1(esk1_2(X25,X26),X25))&v5_relat_1(esk1_2(X25,X26),X26))&v1_funct_1(esk1_2(X25,X26)))&v1_funct_2(esk1_2(X25,X26),X25,X26)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_funct_2])])).
% 0.19/0.44  cnf(c_0_85, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk4_0=k1_xboole_0|~m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(k1_xboole_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.19/0.44  cnf(c_0_86, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_83])).
% 0.19/0.44  cnf(c_0_87, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_24, c_0_83])).
% 0.19/0.44  cnf(c_0_88, negated_conjecture, (v1_funct_2(esk4_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_34, c_0_83])).
% 0.19/0.44  cnf(c_0_89, plain, (m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.44  cnf(c_0_90, plain, (v1_funct_2(esk1_2(X1,X2),X1,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.44  fof(c_0_91, plain, ![X43, X44, X45]:(((v1_funct_1(k2_tops_2(X43,X44,X45))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))&(v1_funct_2(k2_tops_2(X43,X44,X45),X44,X43)|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44))))))&(m1_subset_1(k2_tops_2(X43,X44,X45),k1_zfmisc_1(k2_zfmisc_1(X44,X43)))|(~v1_funct_1(X45)|~v1_funct_2(X45,X43,X44)|~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tops_2])])])).
% 0.19/0.44  cnf(c_0_92, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_85, c_0_83]), c_0_86])])).
% 0.19/0.44  cnf(c_0_93, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_87]), c_0_88])])).
% 0.19/0.44  cnf(c_0_94, plain, (v1_funct_1(esk1_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.44  cnf(c_0_95, plain, (esk1_2(X1,k1_xboole_0)=k1_xboole_0|X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_89]), c_0_90])])).
% 0.19/0.44  cnf(c_0_96, plain, (m1_subset_1(k2_tops_2(X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.44  cnf(c_0_97, plain, (v1_funct_2(k2_tops_2(X1,X2,X3),X2,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_91])).
% 0.19/0.44  cnf(c_0_98, negated_conjecture, (esk4_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_92]), c_0_93])).
% 0.19/0.44  cnf(c_0_99, plain, (X1=k1_xboole_0|v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 0.19/0.44  cnf(c_0_100, plain, (k1_relset_1(X1,X2,k2_tops_2(X2,X1,X3))=X1|X2=k1_xboole_0|~v1_funct_2(X3,X2,X1)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_96]), c_0_97])).
% 0.19/0.44  cnf(c_0_101, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_xboole_0)))), inference(rw,[status(thm)],[c_0_87, c_0_98])).
% 0.19/0.44  cnf(c_0_102, negated_conjecture, (v1_funct_2(k1_xboole_0,u1_struct_0(esk2_0),k1_xboole_0)), inference(rw,[status(thm)],[c_0_88, c_0_98])).
% 0.19/0.44  cnf(c_0_103, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_94, c_0_99])).
% 0.19/0.44  cnf(c_0_104, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),k1_xboole_0,esk4_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_83]), c_0_83])).
% 0.19/0.44  cnf(c_0_105, negated_conjecture, (k1_relset_1(k1_xboole_0,u1_struct_0(esk2_0),k2_tops_2(u1_struct_0(esk2_0),k1_xboole_0,k1_xboole_0))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100, c_0_101]), c_0_102]), c_0_103])])).
% 0.19/0.44  cnf(c_0_106, negated_conjecture, (k2_relset_1(u1_struct_0(esk2_0),k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[c_0_104, c_0_98])).
% 0.19/0.44  cnf(c_0_107, negated_conjecture, (v2_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_35, c_0_98])).
% 0.19/0.44  cnf(c_0_108, negated_conjecture, (k1_relset_1(k1_xboole_0,u1_struct_0(esk2_0),k2_funct_1(k1_xboole_0))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_32]), c_0_106]), c_0_102]), c_0_107]), c_0_103]), c_0_101])])).
% 0.19/0.44  cnf(c_0_109, negated_conjecture, (k1_relat_1(k2_funct_1(k1_xboole_0))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_68, c_0_108])).
% 0.19/0.44  cnf(c_0_110, plain, (v1_relat_1(esk1_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.19/0.44  cnf(c_0_111, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_funct_1(X1)|~v1_relat_1(X1)|~m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_64, c_0_74])).
% 0.19/0.44  cnf(c_0_112, negated_conjecture, (k1_relat_1(k2_funct_1(k1_xboole_0))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_62]), c_0_106]), c_0_102]), c_0_107]), c_0_103]), c_0_101])])).
% 0.19/0.44  cnf(c_0_113, negated_conjecture, (v1_funct_1(k2_funct_1(k1_xboole_0))), inference(rw,[status(thm)],[c_0_40, c_0_98])).
% 0.19/0.44  cnf(c_0_114, plain, (X1=k1_xboole_0|v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_95])).
% 0.19/0.44  cnf(c_0_115, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_67, c_0_23])).
% 0.19/0.44  cnf(c_0_116, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.44  cnf(c_0_117, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))|~v1_relat_1(k2_funct_1(k1_xboole_0))|~m1_subset_1(k2_relat_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])])).
% 0.19/0.44  cnf(c_0_118, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.19/0.44  cnf(c_0_119, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_110, c_0_114])).
% 0.19/0.44  cnf(c_0_120, plain, (m1_subset_1(k2_relat_1(k2_funct_1(X1)),k1_zfmisc_1(X2))|k2_relset_1(X2,X3,X1)!=X3|~v1_funct_2(X1,X2,X3)|~v2_funct_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(spm,[status(thm)],[c_0_115, c_0_62])).
% 0.19/0.44  cnf(c_0_121, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_116])).
% 0.19/0.44  cnf(c_0_122, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))|~m1_subset_1(k2_relat_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117, c_0_118]), c_0_107]), c_0_103]), c_0_119])])).
% 0.19/0.44  cnf(c_0_123, negated_conjecture, (m1_subset_1(k2_relat_1(k2_funct_1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_101]), c_0_106]), c_0_102]), c_0_107]), c_0_103])])).
% 0.19/0.44  cnf(c_0_124, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,u1_struct_0(esk2_0))|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_121, c_0_108])).
% 0.19/0.44  cnf(c_0_125, plain, (k2_tops_2(k1_xboole_0,X1,X2)=k1_xboole_0|X1=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_96]), c_0_97])).
% 0.19/0.44  cnf(c_0_126, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_122, c_0_123])).
% 0.19/0.44  cnf(c_0_127, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124, c_0_62]), c_0_106]), c_0_102]), c_0_107]), c_0_103]), c_0_101])])).
% 0.19/0.44  cnf(c_0_128, negated_conjecture, (~r2_funct_2(u1_struct_0(esk2_0),k1_xboole_0,k2_tops_2(k1_xboole_0,u1_struct_0(esk2_0),k2_funct_1(k1_xboole_0)),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_83]), c_0_83]), c_0_98]), c_0_98])).
% 0.19/0.44  cnf(c_0_129, negated_conjecture, (k2_tops_2(k1_xboole_0,u1_struct_0(esk2_0),k2_funct_1(k1_xboole_0))=k1_xboole_0|u1_struct_0(esk2_0)=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125, c_0_126]), c_0_113])]), c_0_127])).
% 0.19/0.44  fof(c_0_130, plain, ![X37, X38]:(~v1_funct_1(X38)|~v1_funct_2(X38,X37,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X37,X37)))|k1_relset_1(X37,X37,X38)=X37), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t67_funct_2])])).
% 0.19/0.44  cnf(c_0_131, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|~r2_funct_2(u1_struct_0(esk2_0),k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_128, c_0_129])).
% 0.19/0.44  cnf(c_0_132, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_89]), c_0_90]), c_0_94])])).
% 0.19/0.44  cnf(c_0_133, plain, (k1_relset_1(X2,X2,X1)=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_130])).
% 0.19/0.44  cnf(c_0_134, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_131, c_0_132]), c_0_102]), c_0_103]), c_0_101])])).
% 0.19/0.44  cnf(c_0_135, negated_conjecture, (k1_relat_1(k1_xboole_0)!=u1_struct_0(esk2_0)), inference(rw,[status(thm)],[c_0_78, c_0_98])).
% 0.19/0.44  cnf(c_0_136, plain, (X1=k1_relat_1(X2)|~v1_funct_2(X2,X1,X1)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_68, c_0_133])).
% 0.19/0.44  cnf(c_0_137, negated_conjecture, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_101, c_0_134])).
% 0.19/0.44  cnf(c_0_138, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_102, c_0_134])).
% 0.19/0.44  cnf(c_0_139, negated_conjecture, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_135, c_0_134])).
% 0.19/0.44  cnf(c_0_140, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136, c_0_137]), c_0_138]), c_0_103])]), c_0_139]), ['proof']).
% 0.19/0.44  # SZS output end CNFRefutation
% 0.19/0.44  # Proof object total steps             : 141
% 0.19/0.44  # Proof object clause steps            : 104
% 0.19/0.44  # Proof object formula steps           : 37
% 0.19/0.44  # Proof object conjectures             : 65
% 0.19/0.44  # Proof object clause conjectures      : 62
% 0.19/0.44  # Proof object formula conjectures     : 3
% 0.19/0.44  # Proof object initial clauses used    : 34
% 0.19/0.44  # Proof object initial formulas used   : 18
% 0.19/0.44  # Proof object generating inferences   : 51
% 0.19/0.44  # Proof object simplifying inferences  : 143
% 0.19/0.44  # Training examples: 0 positive, 0 negative
% 0.19/0.44  # Parsed axioms                        : 18
% 0.19/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.44  # Initial clauses                      : 46
% 0.19/0.44  # Removed in clause preprocessing      : 1
% 0.19/0.44  # Initial clauses in saturation        : 45
% 0.19/0.44  # Processed clauses                    : 672
% 0.19/0.44  # ...of these trivial                  : 31
% 0.19/0.44  # ...subsumed                          : 218
% 0.19/0.44  # ...remaining for further processing  : 423
% 0.19/0.44  # Other redundant clauses eliminated   : 29
% 0.19/0.44  # Clauses deleted for lack of memory   : 0
% 0.19/0.44  # Backward-subsumed                    : 55
% 0.19/0.44  # Backward-rewritten                   : 124
% 0.19/0.44  # Generated clauses                    : 2221
% 0.19/0.44  # ...of the previous two non-trivial   : 1989
% 0.19/0.44  # Contextual simplify-reflections      : 34
% 0.19/0.44  # Paramodulations                      : 2192
% 0.19/0.44  # Factorizations                       : 0
% 0.19/0.44  # Equation resolutions                 : 29
% 0.19/0.44  # Propositional unsat checks           : 0
% 0.19/0.44  #    Propositional check models        : 0
% 0.19/0.44  #    Propositional check unsatisfiable : 0
% 0.19/0.44  #    Propositional clauses             : 0
% 0.19/0.44  #    Propositional clauses after purity: 0
% 0.19/0.44  #    Propositional unsat core size     : 0
% 0.19/0.44  #    Propositional preprocessing time  : 0.000
% 0.19/0.44  #    Propositional encoding time       : 0.000
% 0.19/0.44  #    Propositional solver time         : 0.000
% 0.19/0.44  #    Success case prop preproc time    : 0.000
% 0.19/0.44  #    Success case prop encoding time   : 0.000
% 0.19/0.44  #    Success case prop solver time     : 0.000
% 0.19/0.44  # Current number of processed clauses  : 194
% 0.19/0.44  #    Positive orientable unit clauses  : 38
% 0.19/0.44  #    Positive unorientable unit clauses: 0
% 0.19/0.44  #    Negative unit clauses             : 3
% 0.19/0.44  #    Non-unit-clauses                  : 153
% 0.19/0.44  # Current number of unprocessed clauses: 976
% 0.19/0.44  # ...number of literals in the above   : 4254
% 0.19/0.44  # Current number of archived formulas  : 0
% 0.19/0.44  # Current number of archived clauses   : 225
% 0.19/0.44  # Clause-clause subsumption calls (NU) : 9426
% 0.19/0.44  # Rec. Clause-clause subsumption calls : 4606
% 0.19/0.44  # Non-unit clause-clause subsumptions  : 294
% 0.19/0.44  # Unit Clause-clause subsumption calls : 487
% 0.19/0.44  # Rewrite failures with RHS unbound    : 0
% 0.19/0.44  # BW rewrite match attempts            : 69
% 0.19/0.44  # BW rewrite match successes           : 18
% 0.19/0.44  # Condensation attempts                : 0
% 0.19/0.44  # Condensation successes               : 0
% 0.19/0.44  # Termbank termtop insertions          : 42255
% 0.19/0.44  
% 0.19/0.44  # -------------------------------------------------
% 0.19/0.44  # User time                : 0.098 s
% 0.19/0.44  # System time              : 0.009 s
% 0.19/0.44  # Total time               : 0.107 s
% 0.19/0.44  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
