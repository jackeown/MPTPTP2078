%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:48 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 480 expanded)
%              Number of clauses        :   46 ( 182 expanded)
%              Number of leaves         :    9 ( 120 expanded)
%              Depth                    :   13
%              Number of atoms          :  232 (2461 expanded)
%              Number of equality atoms :   75 ( 492 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

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

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_10,plain,(
    ! [X85,X86,X87] :
      ( ( ~ v1_funct_2(X87,X85,X86)
        | X85 = k1_relset_1(X85,X86,X87)
        | X86 = k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( X85 != k1_relset_1(X85,X86,X87)
        | v1_funct_2(X87,X85,X86)
        | X86 = k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( ~ v1_funct_2(X87,X85,X86)
        | X85 = k1_relset_1(X85,X86,X87)
        | X85 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( X85 != k1_relset_1(X85,X86,X87)
        | v1_funct_2(X87,X85,X86)
        | X85 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( ~ v1_funct_2(X87,X85,X86)
        | X87 = k1_xboole_0
        | X85 = k1_xboole_0
        | X86 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) )
      & ( X87 != k1_xboole_0
        | v1_funct_2(X87,X85,X86)
        | X85 = k1_xboole_0
        | X86 != k1_xboole_0
        | ~ m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_11,plain,(
    ! [X38,X39] :
      ( ( k2_zfmisc_1(X38,X39) != k1_xboole_0
        | X38 = k1_xboole_0
        | X39 = k1_xboole_0 )
      & ( X38 != k1_xboole_0
        | k2_zfmisc_1(X38,X39) = k1_xboole_0 )
      & ( X39 != k1_xboole_0
        | k2_zfmisc_1(X38,X39) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_12,plain,(
    ! [X72,X73,X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | k1_relset_1(X72,X73,X74) = k1_relat_1(X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_13,plain,(
    ! [X104] :
      ( ( v1_funct_1(X104)
        | ~ v1_relat_1(X104)
        | ~ v1_funct_1(X104) )
      & ( v1_funct_2(X104,k1_relat_1(X104),k2_relat_1(X104))
        | ~ v1_relat_1(X104)
        | ~ v1_funct_1(X104) )
      & ( m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X104),k2_relat_1(X104))))
        | ~ v1_relat_1(X104)
        | ~ v1_funct_1(X104) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_14,plain,(
    ! [X67] :
      ( ( k2_relat_1(X67) = k1_relat_1(k2_funct_1(X67))
        | ~ v2_funct_1(X67)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) )
      & ( k1_relat_1(X67) = k2_relat_1(k2_funct_1(X67))
        | ~ v2_funct_1(X67)
        | ~ v1_relat_1(X67)
        | ~ v1_funct_1(X67) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_15,plain,(
    ! [X58] :
      ( ( v1_relat_1(k2_funct_1(X58))
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58)
        | ~ v2_funct_1(X58) )
      & ( v1_funct_1(k2_funct_1(X58))
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58)
        | ~ v2_funct_1(X58) )
      & ( v2_funct_1(k2_funct_1(X58))
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58)
        | ~ v2_funct_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & v2_funct_1(esk6_0)
    & k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0
    & ( ~ v1_funct_1(k2_funct_1(esk6_0))
      | ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
      | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

fof(c_0_17,plain,(
    ! [X75,X76,X77] :
      ( ~ m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))
      | k2_relset_1(X75,X76,X77) = k2_relat_1(X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_18,plain,(
    ! [X69,X70,X71] :
      ( ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))
      | v1_relat_1(X71) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_19,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( k2_relset_1(esk4_0,esk5_0,esk6_0) = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_30,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relset_1(X2,X3,X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_32,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relat_1(X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_20])).

cnf(c_0_33,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k2_relat_1(esk6_0) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,negated_conjecture,
    ( v2_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_38,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_39,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_20])).

cnf(c_0_40,plain,
    ( v1_funct_2(X1,X2,X3)
    | k1_relat_1(X1) != X2
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(k2_funct_1(esk6_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_42,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_43,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) != esk5_0
    | esk5_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(k2_funct_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk6_0),esk5_0,k2_relat_1(k2_funct_1(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_49,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_50,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_28]),c_0_44])])).

cnf(c_0_51,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_28])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(k2_funct_1(esk6_0)) != esk5_0
    | k1_relat_1(k2_funct_1(esk6_0)) != k1_xboole_0
    | esk5_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk6_0),esk5_0,k1_relat_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_54,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_23]),c_0_34]),c_0_34]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( esk5_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_25]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_relat_1(esk6_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_49]),c_0_35]),c_0_36]),c_0_37])])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk6_0))
    | ~ m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_59])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0))) ),
    inference(sr,[status(thm)],[c_0_60,c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62])])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_25]),c_0_35]),c_0_36]),c_0_37])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.41  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_URBAN_S0Y
% 0.21/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.21/0.41  #
% 0.21/0.41  # Preprocessing time       : 0.031 s
% 0.21/0.41  
% 0.21/0.41  # Proof found!
% 0.21/0.41  # SZS status Theorem
% 0.21/0.41  # SZS output start CNFRefutation
% 0.21/0.41  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 0.21/0.41  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.41  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.21/0.41  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.41  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 0.21/0.41  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 0.21/0.41  fof(fc6_funct_1, axiom, ![X1]:(((v1_relat_1(X1)&v1_funct_1(X1))&v2_funct_1(X1))=>((v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))&v2_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 0.21/0.41  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.41  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.41  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.21/0.41  fof(c_0_10, plain, ![X85, X86, X87]:((((~v1_funct_2(X87,X85,X86)|X85=k1_relset_1(X85,X86,X87)|X86=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))&(X85!=k1_relset_1(X85,X86,X87)|v1_funct_2(X87,X85,X86)|X86=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86)))))&((~v1_funct_2(X87,X85,X86)|X85=k1_relset_1(X85,X86,X87)|X85!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))&(X85!=k1_relset_1(X85,X86,X87)|v1_funct_2(X87,X85,X86)|X85!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))))&((~v1_funct_2(X87,X85,X86)|X87=k1_xboole_0|X85=k1_xboole_0|X86!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86))))&(X87!=k1_xboole_0|v1_funct_2(X87,X85,X86)|X85=k1_xboole_0|X86!=k1_xboole_0|~m1_subset_1(X87,k1_zfmisc_1(k2_zfmisc_1(X85,X86)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.41  fof(c_0_11, plain, ![X38, X39]:((k2_zfmisc_1(X38,X39)!=k1_xboole_0|(X38=k1_xboole_0|X39=k1_xboole_0))&((X38!=k1_xboole_0|k2_zfmisc_1(X38,X39)=k1_xboole_0)&(X39!=k1_xboole_0|k2_zfmisc_1(X38,X39)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.21/0.41  fof(c_0_12, plain, ![X72, X73, X74]:(~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))|k1_relset_1(X72,X73,X74)=k1_relat_1(X74)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.41  fof(c_0_13, plain, ![X104]:(((v1_funct_1(X104)|(~v1_relat_1(X104)|~v1_funct_1(X104)))&(v1_funct_2(X104,k1_relat_1(X104),k2_relat_1(X104))|(~v1_relat_1(X104)|~v1_funct_1(X104))))&(m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X104),k2_relat_1(X104))))|(~v1_relat_1(X104)|~v1_funct_1(X104)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.21/0.41  fof(c_0_14, plain, ![X67]:((k2_relat_1(X67)=k1_relat_1(k2_funct_1(X67))|~v2_funct_1(X67)|(~v1_relat_1(X67)|~v1_funct_1(X67)))&(k1_relat_1(X67)=k2_relat_1(k2_funct_1(X67))|~v2_funct_1(X67)|(~v1_relat_1(X67)|~v1_funct_1(X67)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.21/0.41  fof(c_0_15, plain, ![X58]:(((v1_relat_1(k2_funct_1(X58))|(~v1_relat_1(X58)|~v1_funct_1(X58)|~v2_funct_1(X58)))&(v1_funct_1(k2_funct_1(X58))|(~v1_relat_1(X58)|~v1_funct_1(X58)|~v2_funct_1(X58))))&(v2_funct_1(k2_funct_1(X58))|(~v1_relat_1(X58)|~v1_funct_1(X58)|~v2_funct_1(X58)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).
% 0.21/0.41  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((v2_funct_1(esk6_0)&k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0)&(~v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.21/0.41  fof(c_0_17, plain, ![X75, X76, X77]:(~m1_subset_1(X77,k1_zfmisc_1(k2_zfmisc_1(X75,X76)))|k2_relset_1(X75,X76,X77)=k2_relat_1(X77)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.41  fof(c_0_18, plain, ![X69, X70, X71]:(~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70)))|v1_relat_1(X71)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.41  cnf(c_0_19, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_20, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.41  cnf(c_0_21, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.41  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_23, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_24, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_25, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v2_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.41  cnf(c_0_26, negated_conjecture, (k2_relset_1(esk4_0,esk5_0,esk6_0)=esk5_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.41  cnf(c_0_28, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_29, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.41  cnf(c_0_30, negated_conjecture, (~v1_funct_1(k2_funct_1(esk6_0))|~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_31, plain, (v1_funct_2(X1,X2,X3)|k1_relset_1(X2,X3,X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.21/0.41  cnf(c_0_32, plain, (k1_relset_1(X1,X2,X3)=k1_relat_1(X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_21, c_0_20])).
% 0.21/0.41  cnf(c_0_33, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])).
% 0.21/0.41  cnf(c_0_34, negated_conjecture, (k2_relat_1(esk6_0)=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.21/0.41  cnf(c_0_35, negated_conjecture, (v2_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_36, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_29, c_0_28])).
% 0.21/0.41  cnf(c_0_38, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.21/0.41  cnf(c_0_39, negated_conjecture, (esk5_0!=k1_xboole_0|~v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)|~v1_funct_1(k2_funct_1(esk6_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_30, c_0_20])).
% 0.21/0.41  cnf(c_0_40, plain, (v1_funct_2(X1,X2,X3)|k1_relat_1(X1)!=X2|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.41  cnf(c_0_41, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k2_relat_1(k2_funct_1(esk6_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.21/0.41  cnf(c_0_42, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_23]), c_0_24]), c_0_25])).
% 0.21/0.41  cnf(c_0_43, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.41  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.41  cnf(c_0_45, negated_conjecture, (k1_relat_1(k2_funct_1(esk6_0))!=esk5_0|esk5_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk6_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.21/0.41  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))|k1_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_20])).
% 0.21/0.41  cnf(c_0_47, negated_conjecture, (v1_relat_1(k2_funct_1(esk6_0))), inference(spm,[status(thm)],[c_0_29, c_0_41])).
% 0.21/0.41  cnf(c_0_48, negated_conjecture, (v1_funct_2(k2_funct_1(esk6_0),esk5_0,k2_relat_1(k2_funct_1(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.21/0.41  cnf(c_0_49, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.41  cnf(c_0_50, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_28]), c_0_44])])).
% 0.21/0.41  cnf(c_0_51, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_21, c_0_28])).
% 0.21/0.41  cnf(c_0_52, negated_conjecture, (k1_relat_1(k2_funct_1(esk6_0))!=esk5_0|k1_relat_1(k2_funct_1(esk6_0))!=k1_xboole_0|esk5_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.21/0.41  cnf(c_0_53, negated_conjecture, (v1_funct_2(k2_funct_1(esk6_0),esk5_0,k1_relat_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_35]), c_0_36]), c_0_37])])).
% 0.21/0.41  cnf(c_0_54, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.21/0.41  cnf(c_0_55, negated_conjecture, (esk5_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_23]), c_0_34]), c_0_34]), c_0_35]), c_0_36]), c_0_37])])).
% 0.21/0.41  cnf(c_0_56, negated_conjecture, (esk5_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.21/0.41  cnf(c_0_57, negated_conjecture, (esk5_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_25]), c_0_35]), c_0_36]), c_0_37])])).
% 0.21/0.41  cnf(c_0_58, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_relat_1(esk6_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_49]), c_0_35]), c_0_36]), c_0_37])])).
% 0.21/0.41  cnf(c_0_59, negated_conjecture, (v1_funct_2(k2_funct_1(esk6_0),esk5_0,esk4_0)), inference(sr,[status(thm)],[c_0_56, c_0_57])).
% 0.21/0.41  cnf(c_0_60, negated_conjecture, (esk5_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(spm,[status(thm)],[c_0_58, c_0_54])).
% 0.21/0.41  cnf(c_0_61, negated_conjecture, (~v1_funct_1(k2_funct_1(esk6_0))|~m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_59])])).
% 0.21/0.41  cnf(c_0_62, negated_conjecture, (m1_subset_1(k2_funct_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk4_0)))), inference(sr,[status(thm)],[c_0_60, c_0_57])).
% 0.21/0.41  cnf(c_0_63, negated_conjecture, (~v1_funct_1(k2_funct_1(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62])])).
% 0.21/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_25]), c_0_35]), c_0_36]), c_0_37])]), ['proof']).
% 0.21/0.41  # SZS output end CNFRefutation
% 0.21/0.41  # Proof object total steps             : 65
% 0.21/0.41  # Proof object clause steps            : 46
% 0.21/0.41  # Proof object formula steps           : 19
% 0.21/0.41  # Proof object conjectures             : 31
% 0.21/0.41  # Proof object clause conjectures      : 28
% 0.21/0.41  # Proof object formula conjectures     : 3
% 0.21/0.41  # Proof object initial clauses used    : 18
% 0.21/0.41  # Proof object initial formulas used   : 9
% 0.21/0.41  # Proof object generating inferences   : 24
% 0.21/0.41  # Proof object simplifying inferences  : 46
% 0.21/0.41  # Training examples: 0 positive, 0 negative
% 0.21/0.41  # Parsed axioms                        : 44
% 0.21/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.41  # Initial clauses                      : 80
% 0.21/0.41  # Removed in clause preprocessing      : 11
% 0.21/0.41  # Initial clauses in saturation        : 69
% 0.21/0.41  # Processed clauses                    : 331
% 0.21/0.41  # ...of these trivial                  : 6
% 0.21/0.41  # ...subsumed                          : 116
% 0.21/0.41  # ...remaining for further processing  : 209
% 0.21/0.41  # Other redundant clauses eliminated   : 1
% 0.21/0.41  # Clauses deleted for lack of memory   : 0
% 0.21/0.41  # Backward-subsumed                    : 15
% 0.21/0.41  # Backward-rewritten                   : 13
% 0.21/0.41  # Generated clauses                    : 984
% 0.21/0.41  # ...of the previous two non-trivial   : 798
% 0.21/0.41  # Contextual simplify-reflections      : 32
% 0.21/0.41  # Paramodulations                      : 975
% 0.21/0.41  # Factorizations                       : 0
% 0.21/0.41  # Equation resolutions                 : 4
% 0.21/0.41  # Propositional unsat checks           : 0
% 0.21/0.41  #    Propositional check models        : 0
% 0.21/0.41  #    Propositional check unsatisfiable : 0
% 0.21/0.41  #    Propositional clauses             : 0
% 0.21/0.41  #    Propositional clauses after purity: 0
% 0.21/0.41  #    Propositional unsat core size     : 0
% 0.21/0.41  #    Propositional preprocessing time  : 0.000
% 0.21/0.41  #    Propositional encoding time       : 0.000
% 0.21/0.41  #    Propositional solver time         : 0.000
% 0.21/0.41  #    Success case prop preproc time    : 0.000
% 0.21/0.41  #    Success case prop encoding time   : 0.000
% 0.21/0.41  #    Success case prop solver time     : 0.000
% 0.21/0.41  # Current number of processed clauses  : 175
% 0.21/0.41  #    Positive orientable unit clauses  : 26
% 0.21/0.41  #    Positive unorientable unit clauses: 3
% 0.21/0.41  #    Negative unit clauses             : 3
% 0.21/0.41  #    Non-unit-clauses                  : 143
% 0.21/0.41  # Current number of unprocessed clauses: 518
% 0.21/0.41  # ...number of literals in the above   : 2488
% 0.21/0.41  # Current number of archived formulas  : 0
% 0.21/0.41  # Current number of archived clauses   : 42
% 0.21/0.41  # Clause-clause subsumption calls (NU) : 5900
% 0.21/0.41  # Rec. Clause-clause subsumption calls : 1931
% 0.21/0.41  # Non-unit clause-clause subsumptions  : 133
% 0.21/0.41  # Unit Clause-clause subsumption calls : 175
% 0.21/0.41  # Rewrite failures with RHS unbound    : 0
% 0.21/0.41  # BW rewrite match attempts            : 24
% 0.21/0.41  # BW rewrite match successes           : 9
% 0.21/0.41  # Condensation attempts                : 0
% 0.21/0.41  # Condensation successes               : 0
% 0.21/0.41  # Termbank termtop insertions          : 20636
% 0.21/0.41  
% 0.21/0.41  # -------------------------------------------------
% 0.21/0.41  # User time                : 0.063 s
% 0.21/0.41  # System time              : 0.004 s
% 0.21/0.41  # Total time               : 0.067 s
% 0.21/0.41  # Maximum resident set size: 1628 pages
%------------------------------------------------------------------------------
