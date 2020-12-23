%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:56 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 133 expanded)
%              Number of clauses        :   30 (  48 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  282 ( 800 expanded)
%              Number of equality atoms :   83 ( 220 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   66 (   3 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(t25_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => ( v2_funct_1(X3)
        <=> ! [X4,X5] :
              ( ( r2_hidden(X4,X1)
                & r2_hidden(X5,X1)
                & k1_funct_1(X3,X4) = k1_funct_1(X3,X5) )
             => X4 = X5 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t56_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & r2_hidden(X1,k1_relat_1(X2)) )
       => ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
          & X1 = k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t38_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
        & k8_relset_1(X1,X2,X3,X2) = k1_relset_1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(t6_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_hidden(X3,X1)
       => ( X2 = k1_xboole_0
          | r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X4)
            & r2_hidden(X3,X1) )
         => ( X2 = k1_xboole_0
            | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_funct_2])).

fof(c_0_10,plain,(
    ! [X31,X32,X33,X34,X35] :
      ( ( ~ v2_funct_1(X33)
        | ~ r2_hidden(X34,X31)
        | ~ r2_hidden(X35,X31)
        | k1_funct_1(X33,X34) != k1_funct_1(X33,X35)
        | X34 = X35
        | X32 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r2_hidden(esk4_3(X31,X32,X33),X31)
        | v2_funct_1(X33)
        | X32 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X31)
        | v2_funct_1(X33)
        | X32 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( k1_funct_1(X33,esk4_3(X31,X32,X33)) = k1_funct_1(X33,esk5_3(X31,X32,X33))
        | v2_funct_1(X33)
        | X32 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( esk4_3(X31,X32,X33) != esk5_3(X31,X32,X33)
        | v2_funct_1(X33)
        | X32 = k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( ~ v2_funct_1(X33)
        | ~ r2_hidden(X34,X31)
        | ~ r2_hidden(X35,X31)
        | k1_funct_1(X33,X34) != k1_funct_1(X33,X35)
        | X34 = X35
        | X31 != k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r2_hidden(esk4_3(X31,X32,X33),X31)
        | v2_funct_1(X33)
        | X31 != k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( r2_hidden(esk5_3(X31,X32,X33),X31)
        | v2_funct_1(X33)
        | X31 != k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( k1_funct_1(X33,esk4_3(X31,X32,X33)) = k1_funct_1(X33,esk5_3(X31,X32,X33))
        | v2_funct_1(X33)
        | X31 != k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( esk4_3(X31,X32,X33) != esk5_3(X31,X32,X33)
        | v2_funct_1(X33)
        | X31 != k1_xboole_0
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_2])])])])])).

fof(c_0_11,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,esk7_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
    & v2_funct_1(esk9_0)
    & r2_hidden(esk8_0,esk6_0)
    & esk7_0 != k1_xboole_0
    & k1_funct_1(k2_funct_1(esk9_0),k1_funct_1(esk9_0,esk8_0)) != esk8_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_12,plain,
    ( X2 = X4
    | X5 = k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X2,X3)
    | ~ r2_hidden(X4,X3)
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X5)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v2_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk9_0,X1) != k1_funct_1(esk9_0,X2)
    | ~ r2_hidden(X2,esk6_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_20,plain,(
    ! [X10,X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(esk1_4(X10,X11,X12,X13),k1_relat_1(X10))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk1_4(X10,X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( X13 = k1_funct_1(X10,esk1_4(X10,X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(X16,k1_relat_1(X10))
        | ~ r2_hidden(X16,X11)
        | X15 != k1_funct_1(X10,X16)
        | r2_hidden(X15,X12)
        | X12 != k9_relat_1(X10,X11)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( ~ r2_hidden(esk2_3(X10,X17,X18),X18)
        | ~ r2_hidden(X20,k1_relat_1(X10))
        | ~ r2_hidden(X20,X17)
        | esk2_3(X10,X17,X18) != k1_funct_1(X10,X20)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk3_3(X10,X17,X18),k1_relat_1(X10))
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( r2_hidden(esk3_3(X10,X17,X18),X17)
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) )
      & ( esk2_3(X10,X17,X18) = k1_funct_1(X10,esk3_3(X10,X17,X18))
        | r2_hidden(esk2_3(X10,X17,X18),X18)
        | X18 = k9_relat_1(X10,X17)
        | ~ v1_relat_1(X10)
        | ~ v1_funct_1(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_21,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_22,plain,(
    ! [X8,X9] : v1_relat_1(k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_23,negated_conjecture,
    ( X1 = esk8_0
    | k1_funct_1(esk9_0,X1) != k1_funct_1(esk9_0,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_27,plain,(
    ! [X22,X23] :
      ( ( X22 = k1_funct_1(k2_funct_1(X23),k1_funct_1(X23,X22))
        | ~ v2_funct_1(X23)
        | ~ r2_hidden(X22,k1_relat_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X22 = k1_funct_1(k5_relat_1(X23,k2_funct_1(X23)),X22)
        | ~ v2_funct_1(X23)
        | ~ r2_hidden(X22,k1_relat_1(X23))
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).

fof(c_0_28,plain,(
    ! [X24,X25,X26,X27] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))
      | k7_relset_1(X24,X25,X26,X27) = k9_relat_1(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_29,plain,(
    ! [X28,X29,X30] :
      ( ( k7_relset_1(X28,X29,X30,X28) = k2_relset_1(X28,X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) )
      & ( k8_relset_1(X28,X29,X30,X29) = k1_relset_1(X28,X29,X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).

cnf(c_0_30,negated_conjecture,
    ( esk1_4(X1,esk6_0,X2,X3) = esk8_0
    | k1_funct_1(esk9_0,esk1_4(X1,esk6_0,X2,X3)) != k1_funct_1(esk9_0,esk8_0)
    | X2 != k9_relat_1(X1,esk6_0)
    | ~ r2_hidden(X3,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( X1 = k1_funct_1(X2,esk1_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_16]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk9_0),k1_funct_1(esk9_0,esk8_0)) != esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_34,plain,
    ( X1 = k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))
    | ~ v2_funct_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X38,X39,X40,X41] :
      ( ~ v1_funct_1(X41)
      | ~ v1_funct_2(X41,X38,X39)
      | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | ~ r2_hidden(X40,X38)
      | X39 = k1_xboole_0
      | r2_hidden(k1_funct_1(X41,X40),k2_relset_1(X38,X39,X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).

cnf(c_0_36,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,plain,
    ( k7_relset_1(X1,X2,X3,X1) = k2_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( esk1_4(esk9_0,esk6_0,X1,X2) = esk8_0
    | X2 != k1_funct_1(esk9_0,esk8_0)
    | X1 != k9_relat_1(esk9_0,esk6_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_15]),c_0_32])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k1_relat_1(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_14]),c_0_15]),c_0_32])])).

cnf(c_0_41,plain,
    ( X3 = k1_xboole_0
    | r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( k2_relset_1(X1,X2,X3) = k9_relat_1(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( X1 != k9_relat_1(esk9_0,esk6_0)
    | X2 != k1_funct_1(esk9_0,esk8_0)
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_15]),c_0_32])]),c_0_40])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k1_funct_1(X2,X3),k9_relat_1(X2,X4))
    | ~ v1_funct_2(X2,X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( X1 != k1_funct_1(esk9_0,esk8_0)
    | ~ r2_hidden(X1,k9_relat_1(esk9_0,esk6_0)) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk9_0,X1),k9_relat_1(esk9_0,esk6_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_13]),c_0_15]),c_0_16])]),c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) != k1_funct_1(esk9_0,esk8_0)
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_48,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_47,c_0_19]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.09/0.29  % Computer   : n020.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 19:53:52 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  # Version: 2.5pre002
% 0.09/0.29  # No SInE strategy applied
% 0.09/0.29  # Trying AutoSched0 for 299 seconds
% 0.14/0.32  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.14/0.32  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.32  #
% 0.14/0.32  # Preprocessing time       : 0.025 s
% 0.14/0.32  # Presaturation interreduction done
% 0.14/0.32  
% 0.14/0.32  # Proof found!
% 0.14/0.32  # SZS status Theorem
% 0.14/0.32  # SZS output start CNFRefutation
% 0.14/0.32  fof(t32_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 0.14/0.32  fof(t25_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v2_funct_1(X3)<=>![X4, X5]:(((r2_hidden(X4,X1)&r2_hidden(X5,X1))&k1_funct_1(X3,X4)=k1_funct_1(X3,X5))=>X4=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_funct_2)).
% 0.14/0.32  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.14/0.32  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.32  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.32  fof(t56_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((v2_funct_1(X2)&r2_hidden(X1,k1_relat_1(X2)))=>(X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))&X1=k1_funct_1(k5_relat_1(X2,k2_funct_1(X2)),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 0.14/0.32  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.32  fof(t38_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)&k8_relset_1(X1,X2,X3,X2)=k1_relset_1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 0.14/0.32  fof(t6_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_hidden(X3,X1)=>(X2=k1_xboole_0|r2_hidden(k1_funct_1(X4,X3),k2_relset_1(X1,X2,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 0.14/0.32  fof(c_0_9, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3)))), inference(assume_negation,[status(cth)],[t32_funct_2])).
% 0.14/0.32  fof(c_0_10, plain, ![X31, X32, X33, X34, X35]:(((~v2_funct_1(X33)|(~r2_hidden(X34,X31)|~r2_hidden(X35,X31)|k1_funct_1(X33,X34)!=k1_funct_1(X33,X35)|X34=X35)|X32=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&((((r2_hidden(esk4_3(X31,X32,X33),X31)|v2_funct_1(X33)|X32=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(r2_hidden(esk5_3(X31,X32,X33),X31)|v2_funct_1(X33)|X32=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(k1_funct_1(X33,esk4_3(X31,X32,X33))=k1_funct_1(X33,esk5_3(X31,X32,X33))|v2_funct_1(X33)|X32=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(esk4_3(X31,X32,X33)!=esk5_3(X31,X32,X33)|v2_funct_1(X33)|X32=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))))&((~v2_funct_1(X33)|(~r2_hidden(X34,X31)|~r2_hidden(X35,X31)|k1_funct_1(X33,X34)!=k1_funct_1(X33,X35)|X34=X35)|X31!=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&((((r2_hidden(esk4_3(X31,X32,X33),X31)|v2_funct_1(X33)|X31!=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(r2_hidden(esk5_3(X31,X32,X33),X31)|v2_funct_1(X33)|X31!=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(k1_funct_1(X33,esk4_3(X31,X32,X33))=k1_funct_1(X33,esk5_3(X31,X32,X33))|v2_funct_1(X33)|X31!=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))))))&(esk4_3(X31,X32,X33)!=esk5_3(X31,X32,X33)|v2_funct_1(X33)|X31!=k1_xboole_0|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_funct_2])])])])])).
% 0.14/0.32  fof(c_0_11, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,esk7_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&((v2_funct_1(esk9_0)&r2_hidden(esk8_0,esk6_0))&(esk7_0!=k1_xboole_0&k1_funct_1(k2_funct_1(esk9_0),k1_funct_1(esk9_0,esk8_0))!=esk8_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.14/0.32  cnf(c_0_12, plain, (X2=X4|X5=k1_xboole_0|~v2_funct_1(X1)|~r2_hidden(X2,X3)|~r2_hidden(X4,X3)|k1_funct_1(X1,X2)!=k1_funct_1(X1,X4)|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X5)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.32  cnf(c_0_13, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  cnf(c_0_14, negated_conjecture, (v2_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  cnf(c_0_17, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  cnf(c_0_18, negated_conjecture, (X1=X2|k1_funct_1(esk9_0,X1)!=k1_funct_1(esk9_0,X2)|~r2_hidden(X2,esk6_0)|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])]), c_0_17])).
% 0.14/0.32  cnf(c_0_19, negated_conjecture, (r2_hidden(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  fof(c_0_20, plain, ![X10, X11, X12, X13, X15, X16, X17, X18, X20]:(((((r2_hidden(esk1_4(X10,X11,X12,X13),k1_relat_1(X10))|~r2_hidden(X13,X12)|X12!=k9_relat_1(X10,X11)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(r2_hidden(esk1_4(X10,X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k9_relat_1(X10,X11)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(X13=k1_funct_1(X10,esk1_4(X10,X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k9_relat_1(X10,X11)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(~r2_hidden(X16,k1_relat_1(X10))|~r2_hidden(X16,X11)|X15!=k1_funct_1(X10,X16)|r2_hidden(X15,X12)|X12!=k9_relat_1(X10,X11)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&((~r2_hidden(esk2_3(X10,X17,X18),X18)|(~r2_hidden(X20,k1_relat_1(X10))|~r2_hidden(X20,X17)|esk2_3(X10,X17,X18)!=k1_funct_1(X10,X20))|X18=k9_relat_1(X10,X17)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(((r2_hidden(esk3_3(X10,X17,X18),k1_relat_1(X10))|r2_hidden(esk2_3(X10,X17,X18),X18)|X18=k9_relat_1(X10,X17)|(~v1_relat_1(X10)|~v1_funct_1(X10)))&(r2_hidden(esk3_3(X10,X17,X18),X17)|r2_hidden(esk2_3(X10,X17,X18),X18)|X18=k9_relat_1(X10,X17)|(~v1_relat_1(X10)|~v1_funct_1(X10))))&(esk2_3(X10,X17,X18)=k1_funct_1(X10,esk3_3(X10,X17,X18))|r2_hidden(esk2_3(X10,X17,X18),X18)|X18=k9_relat_1(X10,X17)|(~v1_relat_1(X10)|~v1_funct_1(X10)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.14/0.32  fof(c_0_21, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.32  fof(c_0_22, plain, ![X8, X9]:v1_relat_1(k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.32  cnf(c_0_23, negated_conjecture, (X1=esk8_0|k1_funct_1(esk9_0,X1)!=k1_funct_1(esk9_0,esk8_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.32  cnf(c_0_24, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_25, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.32  cnf(c_0_26, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.32  fof(c_0_27, plain, ![X22, X23]:((X22=k1_funct_1(k2_funct_1(X23),k1_funct_1(X23,X22))|(~v2_funct_1(X23)|~r2_hidden(X22,k1_relat_1(X23)))|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(X22=k1_funct_1(k5_relat_1(X23,k2_funct_1(X23)),X22)|(~v2_funct_1(X23)|~r2_hidden(X22,k1_relat_1(X23)))|(~v1_relat_1(X23)|~v1_funct_1(X23)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t56_funct_1])])])).
% 0.14/0.32  fof(c_0_28, plain, ![X24, X25, X26, X27]:(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X24,X25)))|k7_relset_1(X24,X25,X26,X27)=k9_relat_1(X26,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.32  fof(c_0_29, plain, ![X28, X29, X30]:((k7_relset_1(X28,X29,X30,X28)=k2_relset_1(X28,X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))&(k8_relset_1(X28,X29,X30,X29)=k1_relset_1(X28,X29,X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_relset_1])])])).
% 0.14/0.32  cnf(c_0_30, negated_conjecture, (esk1_4(X1,esk6_0,X2,X3)=esk8_0|k1_funct_1(esk9_0,esk1_4(X1,esk6_0,X2,X3))!=k1_funct_1(esk9_0,esk8_0)|X2!=k9_relat_1(X1,esk6_0)|~r2_hidden(X3,X2)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.14/0.32  cnf(c_0_31, plain, (X1=k1_funct_1(X2,esk1_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_32, negated_conjecture, (v1_relat_1(esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_16]), c_0_26])])).
% 0.14/0.32  cnf(c_0_33, negated_conjecture, (k1_funct_1(k2_funct_1(esk9_0),k1_funct_1(esk9_0,esk8_0))!=esk8_0), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.32  cnf(c_0_34, plain, (X1=k1_funct_1(k2_funct_1(X2),k1_funct_1(X2,X1))|~v2_funct_1(X2)|~r2_hidden(X1,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.14/0.32  fof(c_0_35, plain, ![X38, X39, X40, X41]:(~v1_funct_1(X41)|~v1_funct_2(X41,X38,X39)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|(~r2_hidden(X40,X38)|(X39=k1_xboole_0|r2_hidden(k1_funct_1(X41,X40),k2_relset_1(X38,X39,X41))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_funct_2])])).
% 0.14/0.32  cnf(c_0_36, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.14/0.32  cnf(c_0_37, plain, (k7_relset_1(X1,X2,X3,X1)=k2_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.32  cnf(c_0_38, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.32  cnf(c_0_39, negated_conjecture, (esk1_4(esk9_0,esk6_0,X1,X2)=esk8_0|X2!=k1_funct_1(esk9_0,esk8_0)|X1!=k9_relat_1(esk9_0,esk6_0)|~r2_hidden(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_15]), c_0_32])])).
% 0.14/0.32  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk8_0,k1_relat_1(esk9_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_14]), c_0_15]), c_0_32])])).
% 0.14/0.32  cnf(c_0_41, plain, (X3=k1_xboole_0|r2_hidden(k1_funct_1(X1,X4),k2_relset_1(X2,X3,X1))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.32  cnf(c_0_42, plain, (k2_relset_1(X1,X2,X3)=k9_relat_1(X3,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.14/0.32  cnf(c_0_43, negated_conjecture, (X1!=k9_relat_1(esk9_0,esk6_0)|X2!=k1_funct_1(esk9_0,esk8_0)|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_15]), c_0_32])]), c_0_40])).
% 0.14/0.32  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(k1_funct_1(X2,X3),k9_relat_1(X2,X4))|~v1_funct_2(X2,X4,X1)|~r2_hidden(X3,X4)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.14/0.32  cnf(c_0_45, negated_conjecture, (X1!=k1_funct_1(esk9_0,esk8_0)|~r2_hidden(X1,k9_relat_1(esk9_0,esk6_0))), inference(er,[status(thm)],[c_0_43])).
% 0.14/0.32  cnf(c_0_46, negated_conjecture, (r2_hidden(k1_funct_1(esk9_0,X1),k9_relat_1(esk9_0,esk6_0))|~r2_hidden(X1,esk6_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_13]), c_0_15]), c_0_16])]), c_0_17])).
% 0.14/0.32  cnf(c_0_47, negated_conjecture, (k1_funct_1(esk9_0,X1)!=k1_funct_1(esk9_0,esk8_0)|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.14/0.32  cnf(c_0_48, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_47, c_0_19]), ['proof']).
% 0.14/0.32  # SZS output end CNFRefutation
% 0.14/0.32  # Proof object total steps             : 49
% 0.14/0.32  # Proof object clause steps            : 30
% 0.14/0.32  # Proof object formula steps           : 19
% 0.14/0.32  # Proof object conjectures             : 21
% 0.14/0.32  # Proof object clause conjectures      : 18
% 0.14/0.32  # Proof object formula conjectures     : 3
% 0.14/0.32  # Proof object initial clauses used    : 17
% 0.14/0.32  # Proof object initial formulas used   : 9
% 0.14/0.32  # Proof object generating inferences   : 13
% 0.14/0.32  # Proof object simplifying inferences  : 22
% 0.14/0.32  # Training examples: 0 positive, 0 negative
% 0.14/0.32  # Parsed axioms                        : 9
% 0.14/0.32  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.32  # Initial clauses                      : 33
% 0.14/0.32  # Removed in clause preprocessing      : 0
% 0.14/0.32  # Initial clauses in saturation        : 33
% 0.14/0.32  # Processed clauses                    : 86
% 0.14/0.32  # ...of these trivial                  : 0
% 0.14/0.32  # ...subsumed                          : 1
% 0.14/0.32  # ...remaining for further processing  : 85
% 0.14/0.32  # Other redundant clauses eliminated   : 3
% 0.14/0.32  # Clauses deleted for lack of memory   : 0
% 0.14/0.32  # Backward-subsumed                    : 5
% 0.14/0.32  # Backward-rewritten                   : 0
% 0.14/0.32  # Generated clauses                    : 87
% 0.14/0.32  # ...of the previous two non-trivial   : 71
% 0.14/0.32  # Contextual simplify-reflections      : 0
% 0.14/0.32  # Paramodulations                      : 81
% 0.14/0.32  # Factorizations                       : 0
% 0.14/0.32  # Equation resolutions                 : 6
% 0.14/0.32  # Propositional unsat checks           : 0
% 0.14/0.32  #    Propositional check models        : 0
% 0.14/0.32  #    Propositional check unsatisfiable : 0
% 0.14/0.32  #    Propositional clauses             : 0
% 0.14/0.32  #    Propositional clauses after purity: 0
% 0.14/0.32  #    Propositional unsat core size     : 0
% 0.14/0.32  #    Propositional preprocessing time  : 0.000
% 0.14/0.32  #    Propositional encoding time       : 0.000
% 0.14/0.32  #    Propositional solver time         : 0.000
% 0.14/0.32  #    Success case prop preproc time    : 0.000
% 0.14/0.32  #    Success case prop encoding time   : 0.000
% 0.14/0.32  #    Success case prop solver time     : 0.000
% 0.14/0.32  # Current number of processed clauses  : 47
% 0.14/0.32  #    Positive orientable unit clauses  : 7
% 0.14/0.32  #    Positive unorientable unit clauses: 0
% 0.14/0.32  #    Negative unit clauses             : 3
% 0.14/0.32  #    Non-unit-clauses                  : 37
% 0.14/0.32  # Current number of unprocessed clauses: 51
% 0.14/0.32  # ...number of literals in the above   : 387
% 0.14/0.32  # Current number of archived formulas  : 0
% 0.14/0.32  # Current number of archived clauses   : 38
% 0.14/0.32  # Clause-clause subsumption calls (NU) : 738
% 0.14/0.32  # Rec. Clause-clause subsumption calls : 22
% 0.14/0.32  # Non-unit clause-clause subsumptions  : 5
% 0.14/0.32  # Unit Clause-clause subsumption calls : 0
% 0.14/0.32  # Rewrite failures with RHS unbound    : 0
% 0.14/0.32  # BW rewrite match attempts            : 0
% 0.14/0.32  # BW rewrite match successes           : 0
% 0.14/0.32  # Condensation attempts                : 0
% 0.14/0.32  # Condensation successes               : 0
% 0.14/0.32  # Termbank termtop insertions          : 5344
% 0.14/0.32  
% 0.14/0.32  # -------------------------------------------------
% 0.14/0.32  # User time                : 0.028 s
% 0.14/0.32  # System time              : 0.006 s
% 0.14/0.32  # Total time               : 0.034 s
% 0.14/0.32  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
