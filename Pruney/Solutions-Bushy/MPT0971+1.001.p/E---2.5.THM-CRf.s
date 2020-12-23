%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0971+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:29 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  87 expanded)
%              Number of clauses        :   27 (  36 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 359 expanded)
%              Number of equality atoms :   32 (  71 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(dt_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k1_relset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t17_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
          & ! [X5] :
              ~ ( r2_hidden(X5,X1)
                & k1_funct_1(X4,X5) = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(c_0_9,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | m1_subset_1(k1_relset_1(X19,X20,X21),k1_zfmisc_1(X19)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_relset_1])])).

fof(c_0_10,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | k1_relset_1(X22,X23,X24) = k1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ~ ( r2_hidden(X3,k2_relset_1(X1,X2,X4))
            & ! [X5] :
                ~ ( r2_hidden(X5,X1)
                  & k1_funct_1(X4,X5) = X3 ) ) ) ),
    inference(assume_negation,[status(cth)],[t17_funct_2])).

fof(c_0_12,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | ~ v1_xboole_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_13,plain,
    ( m1_subset_1(k1_relset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_15,negated_conjecture,(
    ! [X40] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk4_0,esk5_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
      & r2_hidden(esk6_0,k2_relset_1(esk4_0,esk5_0,esk7_0))
      & ( ~ r2_hidden(X40,esk4_0)
        | k1_funct_1(esk7_0,X40) != esk6_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_17,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_18,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | m1_subset_1(X30,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relset_1(X1,X3,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_16,c_0_13])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X13,X14,X15,X17] :
      ( ( r2_hidden(esk1_3(X9,X10,X11),k1_relat_1(X9))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( X11 = k1_funct_1(X9,esk1_3(X9,X10,X11))
        | ~ r2_hidden(X11,X10)
        | X10 != k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(X14,k1_relat_1(X9))
        | X13 != k1_funct_1(X9,X14)
        | r2_hidden(X13,X10)
        | X10 != k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( ~ r2_hidden(esk2_2(X9,X15),X15)
        | ~ r2_hidden(X17,k1_relat_1(X9))
        | esk2_2(X9,X15) != k1_funct_1(X9,X17)
        | X15 = k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( r2_hidden(esk3_2(X9,X15),k1_relat_1(X9))
        | r2_hidden(esk2_2(X9,X15),X15)
        | X15 = k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) )
      & ( esk2_2(X9,X15) = k1_funct_1(X9,esk3_2(X9,X15))
        | r2_hidden(esk2_2(X9,X15),X15)
        | X15 = k2_relat_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_23,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,X29)
      | v1_xboole_0(X29)
      | r2_hidden(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(k1_relat_1(esk7_0),k1_zfmisc_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_relat_1(X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_hidden(X1,esk4_0)
    | k1_funct_1(esk7_0,X1) != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( X1 = k1_funct_1(X2,esk1_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_20])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(X1,esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_xboole_0(esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_20])).

cnf(c_0_35,negated_conjecture,
    ( X1 != k2_relat_1(esk7_0)
    | X2 != esk6_0
    | ~ r2_hidden(esk1_3(esk7_0,X1,X2),esk4_0)
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])]),c_0_31])])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_37,negated_conjecture,
    ( X1 != k2_relat_1(esk7_0)
    | X2 != esk6_0
    | ~ r2_hidden(esk1_3(esk7_0,X1,X2),k1_relat_1(esk7_0))
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_38,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_39,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26)))
      | k2_relset_1(X25,X26,X27) = k2_relat_1(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_40,negated_conjecture,
    ( X1 != k2_relat_1(esk7_0)
    | X2 != esk6_0
    | ~ r2_hidden(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_30]),c_0_31])])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relset_1(esk4_0,esk5_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( X1 != esk6_0
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk6_0,k2_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_20])])).

cnf(c_0_45,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_43,c_0_44]),
    [proof]).

%------------------------------------------------------------------------------
