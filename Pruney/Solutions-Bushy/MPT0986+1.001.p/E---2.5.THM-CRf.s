%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0986+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:31 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   27 (  53 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  106 ( 276 expanded)
%              Number of equality atoms :   41 (  89 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X4)
            & r2_hidden(X3,X1) )
         => ( X2 = k1_xboole_0
            | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_funct_2])).

fof(c_0_6,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | k1_relset_1(X11,X12,X13) = k1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_7,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,esk1_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0)))
    & v2_funct_1(esk4_0)
    & r2_hidden(esk3_0,esk1_0)
    & esk2_0 != k1_xboole_0
    & k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_8,plain,(
    ! [X8,X9,X10] :
      ( ( ~ v1_funct_2(X10,X8,X9)
        | X8 = k1_relset_1(X8,X9,X10)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X8 != k1_relset_1(X8,X9,X10)
        | v1_funct_2(X10,X8,X9)
        | X9 = k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( ~ v1_funct_2(X10,X8,X9)
        | X8 = k1_relset_1(X8,X9,X10)
        | X8 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X8 != k1_relset_1(X8,X9,X10)
        | v1_funct_2(X10,X8,X9)
        | X8 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( ~ v1_funct_2(X10,X8,X9)
        | X10 = k1_xboole_0
        | X8 = k1_xboole_0
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) )
      & ( X10 != k1_xboole_0
        | v1_funct_2(X10,X8,X9)
        | X8 = k1_xboole_0
        | X9 != k1_xboole_0
        | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_9,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk1_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_11,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_12,plain,(
    ! [X14,X15] :
      ( ( X14 = k1_funct_1(k2_funct_1(X15),k1_funct_1(X15,X14))
        | ~ v2_funct_1(X15)
        | ~ r2_hidden(X14,k1_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) )
      & ( X14 = k1_funct_1(k5_relat_1(X15,k2_funct_1(X15)),X14)
        | ~ v2_funct_1(X15)
        | ~ r2_hidden(X14,k1_relat_1(X15))
        | ~ v1_relat_1(X15)
        | ~ v1_funct_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

cnf(c_0_13,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( k1_relset_1(esk1_0,esk2_0,esk4_0) = k1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk4_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( k1_relat_1(esk4_0) = esk1_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_10]),c_0_14]),c_0_15])]),c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1)) = X1
    | ~ r2_hidden(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk3_0)) != esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),
    [proof]).

%------------------------------------------------------------------------------
