%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:21 EST 2020

% Result     : Theorem 1.38s
% Output     : CNFRefutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   78 (2042 expanded)
%              Number of clauses        :   63 ( 790 expanded)
%              Number of leaves         :    7 ( 488 expanded)
%              Depth                    :   17
%              Number of atoms          :  229 (11549 expanded)
%              Number of equality atoms :   64 (3001 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(t4_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r1_tarski(k2_relat_1(X2),X1)
       => ( v1_funct_1(X2)
          & v1_funct_2(X2,k1_relat_1(X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(k2_relset_1(X1,X2,X4),X3)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_funct_2])).

fof(c_0_8,plain,(
    ! [X18,X19] :
      ( ( v1_funct_1(X19)
        | ~ r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( v1_funct_2(X19,k1_relat_1(X19),X18)
        | ~ r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) )
      & ( m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X19),X18)))
        | ~ r1_tarski(k2_relat_1(X19),X18)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).

fof(c_0_9,plain,(
    ! [X9,X10,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_relset_1(X9,X10,X11) = k1_relat_1(X11) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_10,plain,(
    ! [X5,X6] :
      ( ~ v1_relat_1(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | v1_relat_1(X6) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)
    & ( esk2_0 != k1_xboole_0
      | esk1_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(esk4_0)
      | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
      | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

fof(c_0_12,plain,(
    ! [X7,X8] : v1_relat_1(k2_zfmisc_1(X7,X8)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_13,plain,(
    ! [X12,X13,X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))
      | k2_relset_1(X12,X13,X14) = k2_relat_1(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X16 = k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X15 = k1_relset_1(X15,X16,X17)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X15 != k1_relset_1(X15,X16,X17)
        | v1_funct_2(X17,X15,X16)
        | X15 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( ~ v1_funct_2(X17,X15,X16)
        | X17 = k1_xboole_0
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( X17 != k1_xboole_0
        | v1_funct_2(X17,X15,X16)
        | X15 = k1_xboole_0
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_15,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_16,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_21,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_22,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( v1_funct_2(X1,k1_relset_1(X2,X3,X1),X4)
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_18])])).

cnf(c_0_28,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)
    | ~ r1_tarski(k2_relat_1(esk4_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_18]),c_0_24]),c_0_25])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24]),c_0_25])])).

cnf(c_0_32,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0
    | esk2_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_18]),c_0_29])])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),esk3_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_29]),c_0_18])])).

cnf(c_0_37,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_funct_1(esk4_0)
    | ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_36])).

cnf(c_0_41,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,esk1_0,esk3_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_24])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_40])).

cnf(c_0_45,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_funct_2(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_27]),c_0_24]),c_0_25])])).

cnf(c_0_47,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_32]),c_0_34])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_51,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_49]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | k1_relset_1(k1_xboole_0,esk2_0,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_51,c_0_48])).

cnf(c_0_55,plain,
    ( k1_relset_1(X1,X2,X3) = k1_relset_1(X4,X5,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_16])).

cnf(c_0_56,negated_conjecture,
    ( esk1_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_52]),c_0_34])).

cnf(c_0_57,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk3_0)
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_45]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_35])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | k1_relset_1(X1,X2,esk4_0) != k1_xboole_0
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_48])])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_56]),c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_40])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_48])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( v1_funct_2(esk4_0,k1_xboole_0,esk2_0)
    | k1_relset_1(esk1_0,esk2_0,esk4_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_61,c_0_18])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | ~ v1_funct_2(esk4_0,k1_xboole_0,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_52]),c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_39])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk3_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_40])).

cnf(c_0_71,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk1_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_22]),c_0_29]),c_0_18])]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_69]),c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,k1_xboole_0)
    | esk1_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_29,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( esk1_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_39,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( ~ v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75])]),c_0_76]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:39:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.38/1.62  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 1.38/1.62  # and selection function PSelectUnlessUniqMaxPos.
% 1.38/1.62  #
% 1.38/1.62  # Preprocessing time       : 0.027 s
% 1.38/1.62  # Presaturation interreduction done
% 1.38/1.62  
% 1.38/1.62  # Proof found!
% 1.38/1.62  # SZS status Theorem
% 1.38/1.62  # SZS output start CNFRefutation
% 1.38/1.62  fof(t8_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 1.38/1.62  fof(t4_funct_2, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r1_tarski(k2_relat_1(X2),X1)=>((v1_funct_1(X2)&v1_funct_2(X2,k1_relat_1(X2),X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 1.38/1.62  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 1.38/1.62  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.38/1.62  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.38/1.62  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 1.38/1.62  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 1.38/1.62  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(k2_relset_1(X1,X2,X4),X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))))), inference(assume_negation,[status(cth)],[t8_funct_2])).
% 1.38/1.62  fof(c_0_8, plain, ![X18, X19]:(((v1_funct_1(X19)|~r1_tarski(k2_relat_1(X19),X18)|(~v1_relat_1(X19)|~v1_funct_1(X19)))&(v1_funct_2(X19,k1_relat_1(X19),X18)|~r1_tarski(k2_relat_1(X19),X18)|(~v1_relat_1(X19)|~v1_funct_1(X19))))&(m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X19),X18)))|~r1_tarski(k2_relat_1(X19),X18)|(~v1_relat_1(X19)|~v1_funct_1(X19)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_funct_2])])])).
% 1.38/1.62  fof(c_0_9, plain, ![X9, X10, X11]:(~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))|k1_relset_1(X9,X10,X11)=k1_relat_1(X11)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 1.38/1.62  fof(c_0_10, plain, ![X5, X6]:(~v1_relat_1(X5)|(~m1_subset_1(X6,k1_zfmisc_1(X5))|v1_relat_1(X6))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 1.38/1.62  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk1_0,esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))))&(r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)&((esk2_0!=k1_xboole_0|esk1_0=k1_xboole_0)&(~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 1.38/1.62  fof(c_0_12, plain, ![X7, X8]:v1_relat_1(k2_zfmisc_1(X7,X8)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.38/1.62  fof(c_0_13, plain, ![X12, X13, X14]:(~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13)))|k2_relset_1(X12,X13,X14)=k2_relat_1(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 1.38/1.62  fof(c_0_14, plain, ![X15, X16, X17]:((((~v1_funct_2(X17,X15,X16)|X15=k1_relset_1(X15,X16,X17)|X16=k1_xboole_0|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(X15!=k1_relset_1(X15,X16,X17)|v1_funct_2(X17,X15,X16)|X16=k1_xboole_0|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&((~v1_funct_2(X17,X15,X16)|X15=k1_relset_1(X15,X16,X17)|X15!=k1_xboole_0|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(X15!=k1_relset_1(X15,X16,X17)|v1_funct_2(X17,X15,X16)|X15!=k1_xboole_0|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))&((~v1_funct_2(X17,X15,X16)|X17=k1_xboole_0|X15=k1_xboole_0|X16!=k1_xboole_0|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))&(X17!=k1_xboole_0|v1_funct_2(X17,X15,X16)|X15=k1_xboole_0|X16!=k1_xboole_0|~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 1.38/1.62  cnf(c_0_15, plain, (v1_funct_2(X1,k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.38/1.62  cnf(c_0_16, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.38/1.62  cnf(c_0_17, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 1.38/1.62  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.38/1.62  cnf(c_0_19, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 1.38/1.62  cnf(c_0_20, negated_conjecture, (r1_tarski(k2_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.38/1.62  cnf(c_0_21, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 1.38/1.62  cnf(c_0_22, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.38/1.62  cnf(c_0_23, plain, (v1_funct_2(X1,k1_relset_1(X2,X3,X1),X4)|~r1_tarski(k2_relat_1(X1),X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 1.38/1.62  cnf(c_0_24, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.38/1.62  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 1.38/1.62  cnf(c_0_26, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.38/1.62  cnf(c_0_27, negated_conjecture, (r1_tarski(k2_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_18])])).
% 1.38/1.62  cnf(c_0_28, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_16, c_0_22])).
% 1.38/1.62  cnf(c_0_29, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.38/1.62  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),X1)|~r1_tarski(k2_relat_1(esk4_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_18]), c_0_24]), c_0_25])])).
% 1.38/1.62  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk4_0),esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24]), c_0_25])])).
% 1.38/1.62  cnf(c_0_32, negated_conjecture, (k1_relat_1(esk4_0)=esk1_0|esk2_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_18]), c_0_29])])).
% 1.38/1.62  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk4_0,k1_relset_1(esk1_0,esk2_0,esk4_0),esk3_0)), inference(spm,[status(thm)],[c_0_30, c_0_27])).
% 1.38/1.62  cnf(c_0_34, negated_conjecture, (esk1_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.38/1.62  cnf(c_0_35, negated_conjecture, (esk2_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.38/1.62  cnf(c_0_36, negated_conjecture, (esk2_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_29]), c_0_18])])).
% 1.38/1.62  cnf(c_0_37, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.38/1.62  cnf(c_0_38, negated_conjecture, (~v1_funct_1(esk4_0)|~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 1.38/1.62  cnf(c_0_39, negated_conjecture, (esk1_0=k1_xboole_0|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 1.38/1.62  cnf(c_0_40, negated_conjecture, (esk1_0=k1_xboole_0|v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_36])).
% 1.38/1.62  cnf(c_0_41, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_37])).
% 1.38/1.62  cnf(c_0_42, negated_conjecture, (~v1_funct_2(esk4_0,esk1_0,esk3_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_24])])).
% 1.38/1.62  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_18, c_0_39])).
% 1.38/1.62  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(spm,[status(thm)],[c_0_18, c_0_40])).
% 1.38/1.62  cnf(c_0_45, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_funct_2(X1,k1_xboole_0,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(spm,[status(thm)],[c_0_16, c_0_41])).
% 1.38/1.62  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk4_0,k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_27]), c_0_24]), c_0_25])])).
% 1.38/1.62  cnf(c_0_47, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.38/1.62  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk2_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 1.38/1.62  cnf(c_0_49, negated_conjecture, (esk1_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_32]), c_0_34])).
% 1.38/1.62  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 1.38/1.62  cnf(c_0_51, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))), inference(er,[status(thm)],[c_0_47])).
% 1.38/1.62  cnf(c_0_52, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|esk2_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_48])).
% 1.38/1.62  cnf(c_0_53, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_49]), c_0_50])).
% 1.38/1.62  cnf(c_0_54, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|k1_relset_1(k1_xboole_0,esk2_0,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_51, c_0_48])).
% 1.38/1.62  cnf(c_0_55, plain, (k1_relset_1(X1,X2,X3)=k1_relset_1(X4,X5,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))), inference(spm,[status(thm)],[c_0_16, c_0_16])).
% 1.38/1.62  cnf(c_0_56, negated_conjecture, (esk1_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_52]), c_0_34])).
% 1.38/1.62  cnf(c_0_57, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk3_0)|~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_50, c_0_48])).
% 1.38/1.62  cnf(c_0_58, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_45]), c_0_53])).
% 1.38/1.62  cnf(c_0_59, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_18, c_0_35])).
% 1.38/1.62  cnf(c_0_60, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 1.38/1.62  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|k1_relset_1(X1,X2,esk4_0)!=k1_xboole_0|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_48])])).
% 1.38/1.62  cnf(c_0_62, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,esk3_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_56]), c_0_57])).
% 1.38/1.62  cnf(c_0_63, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_29, c_0_40])).
% 1.38/1.62  cnf(c_0_64, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(spm,[status(thm)],[c_0_58, c_0_48])).
% 1.38/1.62  cnf(c_0_65, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_59]), c_0_60])).
% 1.38/1.62  cnf(c_0_66, negated_conjecture, (v1_funct_2(esk4_0,k1_xboole_0,esk2_0)|k1_relset_1(esk1_0,esk2_0,esk4_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_61, c_0_18])).
% 1.38/1.62  cnf(c_0_67, negated_conjecture, (esk2_0=k1_xboole_0|~v1_funct_2(esk4_0,k1_xboole_0,esk2_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_52]), c_0_62])).
% 1.38/1.62  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)), inference(sr,[status(thm)],[c_0_63, c_0_64])).
% 1.38/1.62  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_65, c_0_39])).
% 1.38/1.62  cnf(c_0_70, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,esk3_0)|m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_65, c_0_40])).
% 1.38/1.62  cnf(c_0_71, negated_conjecture, (esk2_0=k1_xboole_0|esk1_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_22]), c_0_29]), c_0_18])]), c_0_67])).
% 1.38/1.62  cnf(c_0_72, negated_conjecture, (~m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_68])])).
% 1.38/1.62  cnf(c_0_73, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_69]), c_0_70])).
% 1.38/1.62  cnf(c_0_74, negated_conjecture, (v1_funct_2(esk4_0,esk1_0,k1_xboole_0)|esk1_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_29, c_0_71])).
% 1.38/1.62  cnf(c_0_75, negated_conjecture, (esk1_0=k1_xboole_0), inference(sr,[status(thm)],[c_0_39, c_0_72])).
% 1.38/1.62  cnf(c_0_76, negated_conjecture, (~v1_funct_2(esk4_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_73])).
% 1.38/1.62  cnf(c_0_77, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75])]), c_0_76]), ['proof']).
% 1.38/1.62  # SZS output end CNFRefutation
% 1.38/1.62  # Proof object total steps             : 78
% 1.38/1.62  # Proof object clause steps            : 63
% 1.38/1.62  # Proof object formula steps           : 15
% 1.38/1.62  # Proof object conjectures             : 51
% 1.38/1.62  # Proof object clause conjectures      : 48
% 1.38/1.62  # Proof object formula conjectures     : 3
% 1.38/1.62  # Proof object initial clauses used    : 15
% 1.38/1.62  # Proof object initial formulas used   : 7
% 1.38/1.62  # Proof object generating inferences   : 41
% 1.38/1.62  # Proof object simplifying inferences  : 45
% 1.38/1.62  # Training examples: 0 positive, 0 negative
% 1.38/1.62  # Parsed axioms                        : 7
% 1.38/1.62  # Removed by relevancy pruning/SinE    : 0
% 1.38/1.62  # Initial clauses                      : 19
% 1.38/1.62  # Removed in clause preprocessing      : 1
% 1.38/1.62  # Initial clauses in saturation        : 18
% 1.38/1.62  # Processed clauses                    : 4966
% 1.38/1.62  # ...of these trivial                  : 34
% 1.38/1.62  # ...subsumed                          : 3390
% 1.38/1.62  # ...remaining for further processing  : 1542
% 1.38/1.62  # Other redundant clauses eliminated   : 925
% 1.38/1.62  # Clauses deleted for lack of memory   : 0
% 1.38/1.62  # Backward-subsumed                    : 497
% 1.38/1.62  # Backward-rewritten                   : 771
% 1.38/1.62  # Generated clauses                    : 109045
% 1.38/1.62  # ...of the previous two non-trivial   : 103897
% 1.38/1.62  # Contextual simplify-reflections      : 124
% 1.38/1.62  # Paramodulations                      : 107983
% 1.38/1.62  # Factorizations                       : 125
% 1.38/1.62  # Equation resolutions                 : 925
% 1.38/1.62  # Propositional unsat checks           : 0
% 1.38/1.62  #    Propositional check models        : 0
% 1.38/1.62  #    Propositional check unsatisfiable : 0
% 1.38/1.62  #    Propositional clauses             : 0
% 1.38/1.62  #    Propositional clauses after purity: 0
% 1.38/1.62  #    Propositional unsat core size     : 0
% 1.38/1.62  #    Propositional preprocessing time  : 0.000
% 1.38/1.62  #    Propositional encoding time       : 0.000
% 1.38/1.62  #    Propositional solver time         : 0.000
% 1.38/1.62  #    Success case prop preproc time    : 0.000
% 1.38/1.62  #    Success case prop encoding time   : 0.000
% 1.38/1.62  #    Success case prop solver time     : 0.000
% 1.38/1.62  # Current number of processed clauses  : 239
% 1.38/1.62  #    Positive orientable unit clauses  : 11
% 1.38/1.62  #    Positive unorientable unit clauses: 0
% 1.38/1.62  #    Negative unit clauses             : 1
% 1.38/1.62  #    Non-unit-clauses                  : 227
% 1.38/1.62  # Current number of unprocessed clauses: 97666
% 1.38/1.62  # ...number of literals in the above   : 771991
% 1.38/1.62  # Current number of archived formulas  : 0
% 1.38/1.62  # Current number of archived clauses   : 1299
% 1.38/1.62  # Clause-clause subsumption calls (NU) : 328989
% 1.38/1.62  # Rec. Clause-clause subsumption calls : 62653
% 1.38/1.62  # Non-unit clause-clause subsumptions  : 3946
% 1.38/1.62  # Unit Clause-clause subsumption calls : 1798
% 1.38/1.62  # Rewrite failures with RHS unbound    : 0
% 1.38/1.62  # BW rewrite match attempts            : 71
% 1.38/1.62  # BW rewrite match successes           : 9
% 1.38/1.62  # Condensation attempts                : 0
% 1.38/1.62  # Condensation successes               : 0
% 1.38/1.62  # Termbank termtop insertions          : 2883821
% 1.38/1.62  
% 1.38/1.62  # -------------------------------------------------
% 1.38/1.62  # User time                : 1.213 s
% 1.38/1.62  # System time              : 0.045 s
% 1.38/1.62  # Total time               : 1.259 s
% 1.38/1.62  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
