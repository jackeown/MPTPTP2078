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
% DateTime   : Thu Dec  3 11:00:53 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 347 expanded)
%              Number of clauses        :   47 ( 169 expanded)
%              Number of leaves         :   10 (  89 expanded)
%              Depth                    :   12
%              Number of atoms          :  188 (1066 expanded)
%              Number of equality atoms :   67 ( 321 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t3_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(c_0_10,plain,(
    ! [X11,X12] :
      ( ~ v1_relat_1(X11)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | v1_relat_1(X12) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_11,plain,(
    ! [X9,X10] :
      ( ( ~ m1_subset_1(X9,k1_zfmisc_1(X10))
        | r1_tarski(X9,X10) )
      & ( ~ r1_tarski(X9,X10)
        | m1_subset_1(X9,k1_zfmisc_1(X10)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_12,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_14,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ( v1_funct_1(X1)
          & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    inference(assume_negation,[status(cth)],[t3_funct_2])).

fof(c_0_16,plain,(
    ! [X18,X19,X20] :
      ( ~ v1_relat_1(X20)
      | ~ r1_tarski(k1_relat_1(X20),X18)
      | ~ r1_tarski(k2_relat_1(X20),X19)
      | m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk1_0)
    & v1_funct_1(esk1_0)
    & ( ~ v1_funct_1(esk1_0)
      | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
      | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_20,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_21,plain,(
    ! [X7,X8] :
      ( ( k2_zfmisc_1(X7,X8) != k1_xboole_0
        | X7 = k1_xboole_0
        | X8 = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 )
      & ( X8 != k1_xboole_0
        | k2_zfmisc_1(X7,X8) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_24,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_25,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,plain,(
    ! [X21,X22,X23] :
      ( ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X22 = k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X21 = k1_relset_1(X21,X22,X23)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X21 != k1_relset_1(X21,X22,X23)
        | v1_funct_2(X23,X21,X22)
        | X21 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( ~ v1_funct_2(X23,X21,X22)
        | X23 = k1_xboole_0
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) )
      & ( X23 != k1_xboole_0
        | v1_funct_2(X23,X21,X22)
        | X21 = k1_xboole_0
        | X22 != k1_xboole_0
        | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_29,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_18]),c_0_24]),c_0_18])])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_funct_1(esk1_0)
    | ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_41,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]),c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_36])).

fof(c_0_43,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_32])).

cnf(c_0_45,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))
    | ~ r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_13])).

cnf(c_0_47,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_40]),c_0_24]),c_0_18]),c_0_24])])).

cnf(c_0_48,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | k2_zfmisc_1(X1,X1) != k1_xboole_0 ),
    inference(ef,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_23]),c_0_24]),c_0_23]),c_0_24]),c_0_36]),c_0_18])])).

cnf(c_0_56,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_23]),c_0_36]),c_0_42])])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,X3,X1)
    | k1_relset_1(X3,X1,X2) != X3
    | ~ r1_tarski(X2,k2_zfmisc_1(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_13])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_52])])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_47])).

cnf(c_0_61,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk1_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56])])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0
    | k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0) != k1_relat_1(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_60]),c_0_61]),c_0_62])).

cnf(c_0_65,negated_conjecture,
    ( k2_relat_1(esk1_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_49]),c_0_52])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_65]),c_0_65]),c_0_36]),c_0_18])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.25/3.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S039A
% 3.25/3.43  # and selection function PSelectUnlessUniqMaxPos.
% 3.25/3.43  #
% 3.25/3.43  # Preprocessing time       : 0.028 s
% 3.25/3.43  # Presaturation interreduction done
% 3.25/3.43  
% 3.25/3.43  # Proof found!
% 3.25/3.43  # SZS status Theorem
% 3.25/3.43  # SZS output start CNFRefutation
% 3.25/3.43  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.25/3.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.25/3.43  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.25/3.43  fof(t3_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.25/3.43  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.25/3.43  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.25/3.43  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.25/3.43  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.25/3.43  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.25/3.43  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.25/3.43  fof(c_0_10, plain, ![X11, X12]:(~v1_relat_1(X11)|(~m1_subset_1(X12,k1_zfmisc_1(X11))|v1_relat_1(X12))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 3.25/3.43  fof(c_0_11, plain, ![X9, X10]:((~m1_subset_1(X9,k1_zfmisc_1(X10))|r1_tarski(X9,X10))&(~r1_tarski(X9,X10)|m1_subset_1(X9,k1_zfmisc_1(X10)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.25/3.43  cnf(c_0_12, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 3.25/3.43  cnf(c_0_13, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.25/3.43  fof(c_0_14, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 3.25/3.43  fof(c_0_15, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))))), inference(assume_negation,[status(cth)],[t3_funct_2])).
% 3.25/3.43  fof(c_0_16, plain, ![X18, X19, X20]:(~v1_relat_1(X20)|(~r1_tarski(k1_relat_1(X20),X18)|~r1_tarski(k2_relat_1(X20),X19)|m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 3.25/3.43  cnf(c_0_17, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 3.25/3.43  cnf(c_0_18, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 3.25/3.43  fof(c_0_19, negated_conjecture, ((v1_relat_1(esk1_0)&v1_funct_1(esk1_0))&(~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 3.25/3.43  fof(c_0_20, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.25/3.43  fof(c_0_21, plain, ![X7, X8]:((k2_zfmisc_1(X7,X8)!=k1_xboole_0|(X7=k1_xboole_0|X8=k1_xboole_0))&((X7!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0)&(X8!=k1_xboole_0|k2_zfmisc_1(X7,X8)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 3.25/3.43  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 3.25/3.43  cnf(c_0_23, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 3.25/3.43  cnf(c_0_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 3.25/3.43  cnf(c_0_25, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 3.25/3.43  cnf(c_0_26, negated_conjecture, (v1_relat_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.25/3.43  cnf(c_0_27, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.25/3.43  fof(c_0_28, plain, ![X21, X22, X23]:((((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X22=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))&((~v1_funct_2(X23,X21,X22)|X21=k1_relset_1(X21,X22,X23)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X21!=k1_relset_1(X21,X22,X23)|v1_funct_2(X23,X21,X22)|X21!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))))&((~v1_funct_2(X23,X21,X22)|X23=k1_xboole_0|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22))))&(X23!=k1_xboole_0|v1_funct_2(X23,X21,X22)|X21=k1_xboole_0|X22!=k1_xboole_0|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(X21,X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 3.25/3.43  cnf(c_0_29, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.25/3.43  cnf(c_0_30, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_relat_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_18]), c_0_24]), c_0_18])])).
% 3.25/3.43  cnf(c_0_31, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 3.25/3.43  cnf(c_0_32, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_27])).
% 3.25/3.43  cnf(c_0_33, negated_conjecture, (~v1_funct_1(esk1_0)|~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.25/3.43  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.25/3.43  cnf(c_0_35, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.25/3.43  cnf(c_0_36, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 3.25/3.43  cnf(c_0_37, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31])])).
% 3.25/3.43  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_22, c_0_32])).
% 3.25/3.43  cnf(c_0_39, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 3.25/3.43  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.25/3.43  cnf(c_0_41, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_35]), c_0_36])).
% 3.25/3.43  cnf(c_0_42, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_36])).
% 3.25/3.43  fof(c_0_43, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k1_relset_1(X15,X16,X17)=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 3.25/3.43  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_38, c_0_32])).
% 3.25/3.43  cnf(c_0_45, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.25/3.43  cnf(c_0_46, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))|~r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_39, c_0_13])).
% 3.25/3.43  cnf(c_0_47, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_40]), c_0_24]), c_0_18]), c_0_24])])).
% 3.25/3.43  cnf(c_0_48, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)|k1_relset_1(k1_xboole_0,X1,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.25/3.43  cnf(c_0_49, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.25/3.43  cnf(c_0_50, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 3.25/3.43  cnf(c_0_51, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 3.25/3.43  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk1_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0))))), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 3.25/3.43  cnf(c_0_53, plain, (X1=k1_xboole_0|k2_zfmisc_1(X1,X1)!=k1_xboole_0), inference(ef,[status(thm)],[c_0_45])).
% 3.25/3.43  cnf(c_0_54, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.25/3.43  cnf(c_0_55, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_23]), c_0_24]), c_0_23]), c_0_24]), c_0_36]), c_0_18])])).
% 3.25/3.43  cnf(c_0_56, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_23]), c_0_36]), c_0_42])])).
% 3.25/3.43  cnf(c_0_57, plain, (X1=k1_xboole_0|v1_funct_2(X2,X3,X1)|k1_relset_1(X3,X1,X2)!=X3|~r1_tarski(X2,k2_zfmisc_1(X3,X1))), inference(spm,[status(thm)],[c_0_50, c_0_13])).
% 3.25/3.43  cnf(c_0_58, negated_conjecture, (r1_tarski(esk1_0,k2_zfmisc_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 3.25/3.43  cnf(c_0_59, negated_conjecture, (~v1_funct_2(esk1_0,k1_relat_1(esk1_0),k2_relat_1(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_52])])).
% 3.25/3.43  cnf(c_0_60, plain, (X1=k1_xboole_0|~r1_tarski(k2_zfmisc_1(X1,X1),k1_xboole_0)), inference(spm,[status(thm)],[c_0_53, c_0_47])).
% 3.25/3.43  cnf(c_0_61, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_54])).
% 3.25/3.43  cnf(c_0_62, negated_conjecture, (~r1_tarski(esk1_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56])])).
% 3.25/3.43  cnf(c_0_63, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0|k1_relset_1(k1_relat_1(esk1_0),k2_relat_1(esk1_0),esk1_0)!=k1_relat_1(esk1_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])).
% 3.25/3.43  cnf(c_0_64, negated_conjecture, (~r1_tarski(k2_zfmisc_1(k2_relat_1(esk1_0),k2_relat_1(esk1_0)),k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_60]), c_0_61]), c_0_62])).
% 3.25/3.43  cnf(c_0_65, negated_conjecture, (k2_relat_1(esk1_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_49]), c_0_52])])).
% 3.25/3.43  cnf(c_0_66, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64, c_0_65]), c_0_65]), c_0_36]), c_0_18])]), ['proof']).
% 3.25/3.43  # SZS output end CNFRefutation
% 3.25/3.43  # Proof object total steps             : 67
% 3.25/3.43  # Proof object clause steps            : 47
% 3.25/3.43  # Proof object formula steps           : 20
% 3.25/3.43  # Proof object conjectures             : 18
% 3.25/3.43  # Proof object clause conjectures      : 15
% 3.25/3.43  # Proof object formula conjectures     : 3
% 3.25/3.43  # Proof object initial clauses used    : 18
% 3.25/3.43  # Proof object initial formulas used   : 10
% 3.25/3.43  # Proof object generating inferences   : 20
% 3.25/3.43  # Proof object simplifying inferences  : 42
% 3.25/3.43  # Training examples: 0 positive, 0 negative
% 3.25/3.43  # Parsed axioms                        : 11
% 3.25/3.43  # Removed by relevancy pruning/SinE    : 0
% 3.25/3.43  # Initial clauses                      : 25
% 3.25/3.43  # Removed in clause preprocessing      : 0
% 3.25/3.43  # Initial clauses in saturation        : 25
% 3.25/3.43  # Processed clauses                    : 24249
% 3.25/3.43  # ...of these trivial                  : 659
% 3.25/3.43  # ...subsumed                          : 21908
% 3.25/3.43  # ...remaining for further processing  : 1682
% 3.25/3.43  # Other redundant clauses eliminated   : 1036
% 3.25/3.43  # Clauses deleted for lack of memory   : 0
% 3.25/3.43  # Backward-subsumed                    : 303
% 3.25/3.43  # Backward-rewritten                   : 556
% 3.25/3.43  # Generated clauses                    : 546795
% 3.25/3.43  # ...of the previous two non-trivial   : 418963
% 3.25/3.43  # Contextual simplify-reflections      : 131
% 3.25/3.43  # Paramodulations                      : 545526
% 3.25/3.43  # Factorizations                       : 234
% 3.25/3.43  # Equation resolutions                 : 1036
% 3.25/3.43  # Propositional unsat checks           : 0
% 3.25/3.43  #    Propositional check models        : 0
% 3.25/3.43  #    Propositional check unsatisfiable : 0
% 3.25/3.43  #    Propositional clauses             : 0
% 3.25/3.43  #    Propositional clauses after purity: 0
% 3.25/3.43  #    Propositional unsat core size     : 0
% 3.25/3.43  #    Propositional preprocessing time  : 0.000
% 3.25/3.43  #    Propositional encoding time       : 0.000
% 3.25/3.43  #    Propositional solver time         : 0.000
% 3.25/3.43  #    Success case prop preproc time    : 0.000
% 3.25/3.43  #    Success case prop encoding time   : 0.000
% 3.25/3.43  #    Success case prop solver time     : 0.000
% 3.25/3.43  # Current number of processed clauses  : 791
% 3.25/3.43  #    Positive orientable unit clauses  : 30
% 3.25/3.43  #    Positive unorientable unit clauses: 0
% 3.25/3.43  #    Negative unit clauses             : 7
% 3.25/3.43  #    Non-unit-clauses                  : 754
% 3.25/3.43  # Current number of unprocessed clauses: 390971
% 3.25/3.43  # ...number of literals in the above   : 2197348
% 3.25/3.43  # Current number of archived formulas  : 0
% 3.25/3.43  # Current number of archived clauses   : 883
% 3.25/3.43  # Clause-clause subsumption calls (NU) : 550429
% 3.25/3.43  # Rec. Clause-clause subsumption calls : 134594
% 3.25/3.43  # Non-unit clause-clause subsumptions  : 17608
% 3.25/3.43  # Unit Clause-clause subsumption calls : 3568
% 3.25/3.43  # Rewrite failures with RHS unbound    : 0
% 3.25/3.43  # BW rewrite match attempts            : 98
% 3.25/3.43  # BW rewrite match successes           : 18
% 3.25/3.43  # Condensation attempts                : 0
% 3.25/3.43  # Condensation successes               : 0
% 3.25/3.43  # Termbank termtop insertions          : 11188206
% 3.25/3.44  
% 3.25/3.44  # -------------------------------------------------
% 3.25/3.44  # User time                : 2.955 s
% 3.25/3.44  # System time              : 0.144 s
% 3.25/3.44  # Total time               : 3.099 s
% 3.25/3.44  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
