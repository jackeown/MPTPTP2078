%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:06:33 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   70 (2254 expanded)
%              Number of clauses        :   49 ( 893 expanded)
%              Number of leaves         :   10 ( 541 expanded)
%              Depth                    :   17
%              Number of atoms          :  257 (11994 expanded)
%              Number of equality atoms :   78 (2635 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t115_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X5] :
          ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
            & ! [X6] :
                ~ ( r2_hidden(X6,X1)
                  & r2_hidden(X6,X3)
                  & X5 = k1_funct_1(X4,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

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

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X5] :
            ~ ( r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))
              & ! [X6] :
                  ~ ( r2_hidden(X6,X1)
                    & r2_hidden(X6,X3)
                    & X5 = k1_funct_1(X4,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t115_funct_2])).

fof(c_0_11,plain,(
    ! [X17,X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( r2_hidden(esk2_4(X17,X18,X19,X20),k1_relat_1(X17))
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk2_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( X20 = k1_funct_1(X17,esk2_4(X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(X23,k1_relat_1(X17))
        | ~ r2_hidden(X23,X18)
        | X22 != k1_funct_1(X17,X23)
        | r2_hidden(X22,X19)
        | X19 != k9_relat_1(X17,X18)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( ~ r2_hidden(esk3_3(X17,X24,X25),X25)
        | ~ r2_hidden(X27,k1_relat_1(X17))
        | ~ r2_hidden(X27,X24)
        | esk3_3(X17,X24,X25) != k1_funct_1(X17,X27)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk4_3(X17,X24,X25),k1_relat_1(X17))
        | r2_hidden(esk3_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk4_3(X17,X24,X25),X24)
        | r2_hidden(esk3_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk3_3(X17,X24,X25) = k1_funct_1(X17,esk4_3(X17,X24,X25))
        | r2_hidden(esk3_3(X17,X24,X25),X25)
        | X25 = k9_relat_1(X17,X24)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_12,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_13,negated_conjecture,(
    ! [X46] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))
      & ( ~ r2_hidden(X46,esk5_0)
        | ~ r2_hidden(X46,esk7_0)
        | esk9_0 != k1_funct_1(esk8_0,X46) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_14,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_15,plain,(
    ! [X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k7_relset_1(X34,X35,X36,X37) = k9_relat_1(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_16,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_17,plain,
    ( X1 = k1_funct_1(X2,esk2_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k9_relat_1(X2,X3)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X38,X39,X40] :
      ( ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X39 = k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X38 = k1_relset_1(X38,X39,X40)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X38 != k1_relset_1(X38,X39,X40)
        | v1_funct_2(X40,X38,X39)
        | X38 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( ~ v1_funct_2(X40,X38,X39)
        | X40 = k1_xboole_0
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) )
      & ( X40 != k1_xboole_0
        | v1_funct_2(X40,X38,X39)
        | X38 = k1_xboole_0
        | X39 != k1_xboole_0
        | ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_23,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ r2_hidden(X1,esk7_0)
    | esk9_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3)) = X3
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,negated_conjecture,
    ( k7_relset_1(esk5_0,esk6_0,esk8_0,X1) = k9_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_19])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_32,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)
    | ~ r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)
    | ~ r2_hidden(esk9_0,k9_relat_1(esk8_0,X1)) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26]),c_0_27])])])).

cnf(c_0_36,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0)) ),
    inference(rw,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_19]),c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_26]),c_0_27])])).

cnf(c_0_41,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)
    | ~ r2_hidden(X2,k9_relat_1(esk8_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_26]),c_0_27])])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_43,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_37])])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_19,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_43])).

cnf(c_0_47,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_48,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(esk5_0,k1_xboole_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(rw,[status(thm)],[c_0_33,c_0_43])).

cnf(c_0_50,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | v1_funct_2(esk8_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_48])).

fof(c_0_53,plain,(
    ! [X29,X30] :
      ( ~ r2_hidden(X29,X30)
      | ~ r1_tarski(X30,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_54,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_55,plain,(
    ! [X12,X13,X14,X16] :
      ( ( r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(k4_tarski(esk1_3(X12,X13,X14),X12),X14)
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) )
      & ( ~ r2_hidden(X16,k1_relat_1(X14))
        | ~ r2_hidden(k4_tarski(X16,X12),X14)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X12,k9_relat_1(X14,X13))
        | ~ v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_56,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0) = k1_relat_1(esk8_0)
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ r2_hidden(X1,k9_relat_1(esk8_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_27])]),c_0_62])).

cnf(c_0_64,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_37])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_64])).

cnf(c_0_67,negated_conjecture,
    ( v1_relat_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_65])).

cnf(c_0_68,plain,
    ( ~ r2_hidden(X1,k9_relat_1(k1_xboole_0,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_69,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_65]),c_0_68]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:11:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.028 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t115_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 0.14/0.39  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 0.14/0.39  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.39  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.39  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.39  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.39  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.14/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X5]:~((r2_hidden(X5,k7_relset_1(X1,X2,X4,X3))&![X6]:~(((r2_hidden(X6,X1)&r2_hidden(X6,X3))&X5=k1_funct_1(X4,X6))))))), inference(assume_negation,[status(cth)],[t115_funct_2])).
% 0.14/0.39  fof(c_0_11, plain, ![X17, X18, X19, X20, X22, X23, X24, X25, X27]:(((((r2_hidden(esk2_4(X17,X18,X19,X20),k1_relat_1(X17))|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(esk2_4(X17,X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(X20=k1_funct_1(X17,esk2_4(X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(~r2_hidden(X23,k1_relat_1(X17))|~r2_hidden(X23,X18)|X22!=k1_funct_1(X17,X23)|r2_hidden(X22,X19)|X19!=k9_relat_1(X17,X18)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&((~r2_hidden(esk3_3(X17,X24,X25),X25)|(~r2_hidden(X27,k1_relat_1(X17))|~r2_hidden(X27,X24)|esk3_3(X17,X24,X25)!=k1_funct_1(X17,X27))|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(((r2_hidden(esk4_3(X17,X24,X25),k1_relat_1(X17))|r2_hidden(esk3_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(esk4_3(X17,X24,X25),X24)|r2_hidden(esk3_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(esk3_3(X17,X24,X25)=k1_funct_1(X17,esk4_3(X17,X24,X25))|r2_hidden(esk3_3(X17,X24,X25),X25)|X25=k9_relat_1(X17,X24)|(~v1_relat_1(X17)|~v1_funct_1(X17)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.14/0.39  fof(c_0_12, plain, ![X8, X9]:(~v1_relat_1(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_relat_1(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.39  fof(c_0_13, negated_conjecture, ![X46]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))&(~r2_hidden(X46,esk5_0)|~r2_hidden(X46,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X46)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.14/0.39  fof(c_0_14, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.39  fof(c_0_15, plain, ![X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k7_relset_1(X34,X35,X36,X37)=k9_relat_1(X36,X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.39  fof(c_0_16, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.39  cnf(c_0_17, plain, (X1=k1_funct_1(X2,esk2_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k9_relat_1(X2,X3)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_18, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.39  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_20, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_21, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  fof(c_0_22, plain, ![X38, X39, X40]:((((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X39=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))&((~v1_funct_2(X40,X38,X39)|X38=k1_relset_1(X38,X39,X40)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X38!=k1_relset_1(X38,X39,X40)|v1_funct_2(X40,X38,X39)|X38!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))))&((~v1_funct_2(X40,X38,X39)|X40=k1_xboole_0|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39))))&(X40!=k1_xboole_0|v1_funct_2(X40,X38,X39)|X38=k1_xboole_0|X39!=k1_xboole_0|~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.39  cnf(c_0_23, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_24, negated_conjecture, (~r2_hidden(X1,esk5_0)|~r2_hidden(X1,esk7_0)|esk9_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_25, plain, (k1_funct_1(X1,esk2_4(X1,X2,k9_relat_1(X1,X2),X3))=X3|~v1_funct_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])])).
% 0.14/0.39  cnf(c_0_28, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_29, negated_conjecture, (r2_hidden(esk9_0,k7_relset_1(esk5_0,esk6_0,esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (k7_relset_1(esk5_0,esk6_0,esk8_0,X1)=k9_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_19])).
% 0.14/0.39  cnf(c_0_31, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),k1_relat_1(X1))|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.39  cnf(c_0_32, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk5_0)|~r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),esk9_0),esk7_0)|~r2_hidden(esk9_0,k9_relat_1(esk8_0,X1))), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26]), c_0_27])])])).
% 0.14/0.39  cnf(c_0_36, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_funct_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_28])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (r2_hidden(esk9_0,k9_relat_1(esk8_0,esk7_0))), inference(rw,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  cnf(c_0_38, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),k1_relat_1(X1))|~v1_funct_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_31])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_19]), c_0_33]), c_0_34])])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk2_4(esk8_0,esk7_0,k9_relat_1(esk8_0,esk7_0),esk9_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_26]), c_0_27])])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (esk6_0=k1_xboole_0|r2_hidden(esk2_4(esk8_0,X1,k9_relat_1(esk8_0,X1),X2),esk5_0)|~r2_hidden(X2,k9_relat_1(esk8_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_26]), c_0_27])])).
% 0.14/0.39  cnf(c_0_42, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_43, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_37])])).
% 0.14/0.39  cnf(c_0_44, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_42])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_19, c_0_43])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_34, c_0_43])).
% 0.14/0.39  cnf(c_0_47, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (esk8_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 0.14/0.39  cnf(c_0_49, negated_conjecture, (k1_relset_1(esk5_0,k1_xboole_0,esk8_0)=k1_relat_1(esk8_0)), inference(rw,[status(thm)],[c_0_33, c_0_43])).
% 0.14/0.39  cnf(c_0_50, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_47])).
% 0.14/0.39  cnf(c_0_51, negated_conjecture, (esk8_0=k1_xboole_0|m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_45, c_0_48])).
% 0.14/0.39  cnf(c_0_52, negated_conjecture, (esk8_0=k1_xboole_0|v1_funct_2(esk8_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_48])).
% 0.14/0.39  fof(c_0_53, plain, ![X29, X30]:(~r2_hidden(X29,X30)|~r1_tarski(X30,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.39  fof(c_0_54, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.39  fof(c_0_55, plain, ![X12, X13, X14, X16]:((((r2_hidden(esk1_3(X12,X13,X14),k1_relat_1(X14))|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14))&(r2_hidden(k4_tarski(esk1_3(X12,X13,X14),X12),X14)|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14)))&(r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14)))&(~r2_hidden(X16,k1_relat_1(X14))|~r2_hidden(k4_tarski(X16,X12),X14)|~r2_hidden(X16,X13)|r2_hidden(X12,k9_relat_1(X14,X13))|~v1_relat_1(X14))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.14/0.39  cnf(c_0_56, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0)=k1_relat_1(esk8_0)|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_49, c_0_48])).
% 0.14/0.39  cnf(c_0_57, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.14/0.39  cnf(c_0_58, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.14/0.39  cnf(c_0_59, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.14/0.39  cnf(c_0_60, plain, (r2_hidden(esk1_3(X1,X2,X3),k1_relat_1(X3))|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.14/0.39  cnf(c_0_62, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.14/0.39  cnf(c_0_63, negated_conjecture, (esk8_0=k1_xboole_0|~r2_hidden(X1,k9_relat_1(esk8_0,X2))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_27])]), c_0_62])).
% 0.14/0.39  cnf(c_0_64, plain, (r2_hidden(k4_tarski(esk1_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.39  cnf(c_0_65, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_37])).
% 0.14/0.39  cnf(c_0_66, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))|~v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_64])).
% 0.14/0.39  cnf(c_0_67, negated_conjecture, (v1_relat_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_27, c_0_65])).
% 0.14/0.39  cnf(c_0_68, plain, (~r2_hidden(X1,k9_relat_1(k1_xboole_0,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.14/0.39  cnf(c_0_69, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_65]), c_0_68]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 70
% 0.14/0.39  # Proof object clause steps            : 49
% 0.14/0.39  # Proof object formula steps           : 21
% 0.14/0.39  # Proof object conjectures             : 30
% 0.14/0.39  # Proof object clause conjectures      : 27
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 19
% 0.14/0.39  # Proof object initial formulas used   : 10
% 0.14/0.39  # Proof object generating inferences   : 18
% 0.14/0.39  # Proof object simplifying inferences  : 38
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 10
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 29
% 0.14/0.39  # Removed in clause preprocessing      : 0
% 0.14/0.39  # Initial clauses in saturation        : 29
% 0.14/0.39  # Processed clauses                    : 229
% 0.14/0.39  # ...of these trivial                  : 1
% 0.14/0.39  # ...subsumed                          : 132
% 0.14/0.39  # ...remaining for further processing  : 95
% 0.14/0.39  # Other redundant clauses eliminated   : 12
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 46
% 0.14/0.39  # Generated clauses                    : 471
% 0.14/0.39  # ...of the previous two non-trivial   : 489
% 0.14/0.39  # Contextual simplify-reflections      : 1
% 0.14/0.39  # Paramodulations                      : 461
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 12
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 41
% 0.14/0.39  #    Positive orientable unit clauses  : 8
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 3
% 0.14/0.39  #    Non-unit-clauses                  : 30
% 0.14/0.39  # Current number of unprocessed clauses: 277
% 0.14/0.39  # ...number of literals in the above   : 1001
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 46
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 509
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 325
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 93
% 0.14/0.39  # Unit Clause-clause subsumption calls : 29
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 5
% 0.14/0.39  # BW rewrite match successes           : 5
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 8886
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.038 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.044 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
