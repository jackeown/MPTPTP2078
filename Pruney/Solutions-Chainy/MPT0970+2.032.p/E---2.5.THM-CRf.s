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
% DateTime   : Thu Dec  3 11:01:31 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   66 (1656 expanded)
%              Number of clauses        :   46 ( 660 expanded)
%              Number of leaves         :   10 ( 387 expanded)
%              Depth                    :   16
%              Number of atoms          :  240 (7929 expanded)
%              Number of equality atoms :  103 (2559 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] :
                  ~ ( r2_hidden(X5,X1)
                    & X4 = k1_funct_1(X3,X5) ) )
       => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t23_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X5,X4),X3) )
      <=> k2_relset_1(X1,X2,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ! [X4] :
              ~ ( r2_hidden(X4,X2)
                & ! [X5] :
                    ~ ( r2_hidden(X5,X1)
                      & X4 = k1_funct_1(X3,X5) ) )
         => k2_relset_1(X1,X2,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t16_funct_2])).

fof(c_0_11,plain,(
    ! [X34,X35,X36] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | k2_relset_1(X34,X35,X36) = k2_relat_1(X36) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X50] :
      ( v1_funct_1(esk11_0)
      & v1_funct_2(esk11_0,esk9_0,esk10_0)
      & m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))
      & ( r2_hidden(esk12_1(X50),esk9_0)
        | ~ r2_hidden(X50,esk10_0) )
      & ( X50 = k1_funct_1(esk11_0,esk12_1(X50))
        | ~ r2_hidden(X50,esk10_0) )
      & k2_relset_1(esk9_0,esk10_0,esk11_0) != esk10_0 ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).

fof(c_0_13,plain,(
    ! [X31,X32,X33] :
      ( ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))
      | k1_relset_1(X31,X32,X33) = k1_relat_1(X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_14,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,plain,(
    ! [X18,X19,X20,X22,X23,X24,X26] :
      ( ( r2_hidden(esk4_3(X18,X19,X20),k1_relat_1(X18))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( X20 = k1_funct_1(X18,esk4_3(X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(X23,k1_relat_1(X18))
        | X22 != k1_funct_1(X18,X23)
        | r2_hidden(X22,X19)
        | X19 != k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( ~ r2_hidden(esk5_2(X18,X24),X24)
        | ~ r2_hidden(X26,k1_relat_1(X18))
        | esk5_2(X18,X24) != k1_funct_1(X18,X26)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( r2_hidden(esk6_2(X18,X24),k1_relat_1(X18))
        | r2_hidden(esk5_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) )
      & ( esk5_2(X18,X24) = k1_funct_1(X18,esk6_2(X18,X24))
        | r2_hidden(esk5_2(X18,X24),X24)
        | X24 = k2_relat_1(X18)
        | ~ v1_relat_1(X18)
        | ~ v1_funct_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_17,plain,(
    ! [X44,X45,X46] :
      ( ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X46 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X46 != k1_xboole_0
        | v1_funct_2(X46,X44,X45)
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_18,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_19,plain,(
    ! [X28,X29,X30] :
      ( ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_relat_1(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X37,X38,X39,X41,X42] :
      ( ( r2_hidden(esk7_3(X37,X38,X39),X38)
        | k2_relset_1(X37,X38,X39) = X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( ~ r2_hidden(k4_tarski(X41,esk7_3(X37,X38,X39)),X39)
        | k2_relset_1(X37,X38,X39) = X38
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) )
      & ( k2_relset_1(X37,X38,X39) != X38
        | ~ r2_hidden(X42,X38)
        | r2_hidden(k4_tarski(esk8_4(X37,X38,X39,X42),X42),X39)
        | ~ m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(esk9_0,esk10_0,esk11_0) != esk10_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( k2_relset_1(esk9_0,esk10_0,esk11_0) = k2_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X10,X11,X12,X13,X15] :
      ( ( ~ r2_hidden(X8,X7)
        | r2_hidden(k4_tarski(esk1_3(X6,X7,X8),X8),X6)
        | X7 != k2_relat_1(X6) )
      & ( ~ r2_hidden(k4_tarski(X11,X10),X6)
        | r2_hidden(X10,X7)
        | X7 != k2_relat_1(X6) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | ~ r2_hidden(k4_tarski(X15,esk2_2(X12,X13)),X12)
        | X13 = k2_relat_1(X12) )
      & ( r2_hidden(esk2_2(X12,X13),X13)
        | r2_hidden(k4_tarski(esk3_2(X12,X13),esk2_2(X12,X13)),X12)
        | X13 = k2_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk11_0,esk9_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_27,negated_conjecture,
    ( k1_relset_1(esk9_0,esk10_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_15])).

cnf(c_0_28,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r2_hidden(esk7_3(X1,X2,X3),X2)
    | k2_relset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( k2_relat_1(esk11_0) != esk10_0 ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( k2_relset_1(X2,X3,X4) = X3
    | ~ r2_hidden(k4_tarski(X1,esk7_3(X2,X3,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_34,negated_conjecture,
    ( k1_relat_1(esk11_0) = esk9_0
    | esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_15])])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_15])).

cnf(c_0_37,negated_conjecture,
    ( X1 = k1_funct_1(esk11_0,esk12_1(X1))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk7_3(esk9_0,esk10_0,esk11_0),esk10_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_15]),c_0_22]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(k4_tarski(X1,esk7_3(esk9_0,esk10_0,esk11_0)),esk11_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_15]),c_0_22]),c_0_30])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | r2_hidden(k1_funct_1(esk11_0,X1),k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_36])])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk11_0,esk12_1(esk7_3(esk9_0,esk10_0,esk11_0))) = esk7_3(esk9_0,esk10_0,esk11_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( ~ r2_hidden(esk7_3(esk9_0,esk10_0,esk11_0),k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,negated_conjecture,
    ( esk10_0 = k1_xboole_0
    | ~ r2_hidden(esk12_1(esk7_3(esk9_0,esk10_0,esk11_0)),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_43])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk12_1(X1),esk9_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_47,negated_conjecture,
    ( esk10_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_38])])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,k1_xboole_0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) ),
    inference(er,[status(thm)],[c_0_46])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk11_0,esk9_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_26,c_0_47])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_47])).

cnf(c_0_51,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_52,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])])).

cnf(c_0_53,negated_conjecture,
    ( k1_relset_1(esk9_0,k1_xboole_0,esk11_0) = k1_relat_1(esk11_0) ),
    inference(rw,[status(thm)],[c_0_27,c_0_47])).

cnf(c_0_54,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | v1_funct_2(esk11_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( esk11_0 = k1_xboole_0
    | m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_50,c_0_52])).

fof(c_0_57,plain,(
    ! [X17] :
      ( ( k1_relat_1(X17) != k1_xboole_0
        | k2_relat_1(X17) = k1_xboole_0
        | ~ v1_relat_1(X17) )
      & ( k2_relat_1(X17) != k1_xboole_0
        | k1_relat_1(X17) = k1_xboole_0
        | ~ v1_relat_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_58,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk11_0) = k1_relat_1(esk11_0)
    | esk11_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk11_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_60,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( k1_relat_1(esk11_0) = k1_xboole_0
    | esk11_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( k2_relat_1(esk11_0) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_30,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( esk11_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_36])]),c_0_62])).

cnf(c_0_64,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_65,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63]),c_0_64])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:45:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.39  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.39  #
% 0.13/0.39  # Preprocessing time       : 0.028 s
% 0.13/0.39  # Presaturation interreduction done
% 0.13/0.39  
% 0.13/0.39  # Proof found!
% 0.13/0.39  # SZS status Theorem
% 0.13/0.39  # SZS output start CNFRefutation
% 0.13/0.39  fof(t16_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 0.13/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.13/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.39  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.13/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.39  fof(t23_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X5,X4),X3))))<=>k2_relset_1(X1,X2,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 0.13/0.39  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.39  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.13/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.39  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~((r2_hidden(X5,X1)&X4=k1_funct_1(X3,X5)))))=>k2_relset_1(X1,X2,X3)=X2))), inference(assume_negation,[status(cth)],[t16_funct_2])).
% 0.13/0.39  fof(c_0_11, plain, ![X34, X35, X36]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|k2_relset_1(X34,X35,X36)=k2_relat_1(X36)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.13/0.39  fof(c_0_12, negated_conjecture, ![X50]:(((v1_funct_1(esk11_0)&v1_funct_2(esk11_0,esk9_0,esk10_0))&m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0))))&(((r2_hidden(esk12_1(X50),esk9_0)|~r2_hidden(X50,esk10_0))&(X50=k1_funct_1(esk11_0,esk12_1(X50))|~r2_hidden(X50,esk10_0)))&k2_relset_1(esk9_0,esk10_0,esk11_0)!=esk10_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])])).
% 0.13/0.39  fof(c_0_13, plain, ![X31, X32, X33]:(~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))|k1_relset_1(X31,X32,X33)=k1_relat_1(X33)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.39  cnf(c_0_14, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.39  cnf(c_0_15, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,esk10_0)))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  fof(c_0_16, plain, ![X18, X19, X20, X22, X23, X24, X26]:((((r2_hidden(esk4_3(X18,X19,X20),k1_relat_1(X18))|~r2_hidden(X20,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(X20=k1_funct_1(X18,esk4_3(X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&(~r2_hidden(X23,k1_relat_1(X18))|X22!=k1_funct_1(X18,X23)|r2_hidden(X22,X19)|X19!=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18))))&((~r2_hidden(esk5_2(X18,X24),X24)|(~r2_hidden(X26,k1_relat_1(X18))|esk5_2(X18,X24)!=k1_funct_1(X18,X26))|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&((r2_hidden(esk6_2(X18,X24),k1_relat_1(X18))|r2_hidden(esk5_2(X18,X24),X24)|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))&(esk5_2(X18,X24)=k1_funct_1(X18,esk6_2(X18,X24))|r2_hidden(esk5_2(X18,X24),X24)|X24=k2_relat_1(X18)|(~v1_relat_1(X18)|~v1_funct_1(X18)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.13/0.39  fof(c_0_17, plain, ![X44, X45, X46]:((((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&((~v1_funct_2(X46,X44,X45)|X46=k1_xboole_0|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X46!=k1_xboole_0|v1_funct_2(X46,X44,X45)|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.39  cnf(c_0_18, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.39  fof(c_0_19, plain, ![X28, X29, X30]:(~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_relat_1(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.39  fof(c_0_20, plain, ![X37, X38, X39, X41, X42]:(((r2_hidden(esk7_3(X37,X38,X39),X38)|k2_relset_1(X37,X38,X39)=X38|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))&(~r2_hidden(k4_tarski(X41,esk7_3(X37,X38,X39)),X39)|k2_relset_1(X37,X38,X39)=X38|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38)))))&(k2_relset_1(X37,X38,X39)!=X38|(~r2_hidden(X42,X38)|r2_hidden(k4_tarski(esk8_4(X37,X38,X39,X42),X42),X39))|~m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X37,X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t23_relset_1])])])])])])).
% 0.13/0.39  cnf(c_0_21, negated_conjecture, (k2_relset_1(esk9_0,esk10_0,esk11_0)!=esk10_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_22, negated_conjecture, (k2_relset_1(esk9_0,esk10_0,esk11_0)=k2_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.39  fof(c_0_23, plain, ![X6, X7, X8, X10, X11, X12, X13, X15]:(((~r2_hidden(X8,X7)|r2_hidden(k4_tarski(esk1_3(X6,X7,X8),X8),X6)|X7!=k2_relat_1(X6))&(~r2_hidden(k4_tarski(X11,X10),X6)|r2_hidden(X10,X7)|X7!=k2_relat_1(X6)))&((~r2_hidden(esk2_2(X12,X13),X13)|~r2_hidden(k4_tarski(X15,esk2_2(X12,X13)),X12)|X13=k2_relat_1(X12))&(r2_hidden(esk2_2(X12,X13),X13)|r2_hidden(k4_tarski(esk3_2(X12,X13),esk2_2(X12,X13)),X12)|X13=k2_relat_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.39  cnf(c_0_24, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.39  cnf(c_0_25, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk11_0,esk9_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_27, negated_conjecture, (k1_relset_1(esk9_0,esk10_0,esk11_0)=k1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_18, c_0_15])).
% 0.13/0.39  cnf(c_0_28, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.39  cnf(c_0_29, plain, (r2_hidden(esk7_3(X1,X2,X3),X2)|k2_relset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_30, negated_conjecture, (k2_relat_1(esk11_0)!=esk10_0), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.39  cnf(c_0_31, plain, (k2_relset_1(X2,X3,X4)=X3|~r2_hidden(k4_tarski(X1,esk7_3(X2,X3,X4)),X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.39  cnf(c_0_32, plain, (r2_hidden(k4_tarski(esk1_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.13/0.39  cnf(c_0_33, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.13/0.39  cnf(c_0_34, negated_conjecture, (k1_relat_1(esk11_0)=esk9_0|esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_15])])).
% 0.13/0.39  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_28, c_0_15])).
% 0.13/0.39  cnf(c_0_37, negated_conjecture, (X1=k1_funct_1(esk11_0,esk12_1(X1))|~r2_hidden(X1,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(esk7_3(esk9_0,esk10_0,esk11_0),esk10_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_15]), c_0_22]), c_0_30])).
% 0.13/0.39  cnf(c_0_39, negated_conjecture, (~r2_hidden(k4_tarski(X1,esk7_3(esk9_0,esk10_0,esk11_0)),esk11_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_15]), c_0_22]), c_0_30])).
% 0.13/0.39  cnf(c_0_40, plain, (r2_hidden(k4_tarski(esk1_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_32])).
% 0.13/0.39  cnf(c_0_41, negated_conjecture, (esk10_0=k1_xboole_0|r2_hidden(k1_funct_1(esk11_0,X1),k2_relat_1(esk11_0))|~r2_hidden(X1,esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_36])])).
% 0.13/0.39  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk11_0,esk12_1(esk7_3(esk9_0,esk10_0,esk11_0)))=esk7_3(esk9_0,esk10_0,esk11_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.13/0.39  cnf(c_0_43, negated_conjecture, (~r2_hidden(esk7_3(esk9_0,esk10_0,esk11_0),k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.13/0.39  cnf(c_0_44, negated_conjecture, (esk10_0=k1_xboole_0|~r2_hidden(esk12_1(esk7_3(esk9_0,esk10_0,esk11_0)),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_43])).
% 0.13/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(esk12_1(X1),esk9_0)|~r2_hidden(X1,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.39  cnf(c_0_46, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X1,X2,X3)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_47, negated_conjecture, (esk10_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_38])])).
% 0.13/0.39  cnf(c_0_48, plain, (X1=k1_xboole_0|X2=k1_xboole_0|~v1_funct_2(X2,X1,k1_xboole_0)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))), inference(er,[status(thm)],[c_0_46])).
% 0.13/0.39  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk11_0,esk9_0,k1_xboole_0)), inference(rw,[status(thm)],[c_0_26, c_0_47])).
% 0.13/0.39  cnf(c_0_50, negated_conjecture, (m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(esk9_0,k1_xboole_0)))), inference(rw,[status(thm)],[c_0_15, c_0_47])).
% 0.13/0.39  cnf(c_0_51, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.39  cnf(c_0_52, negated_conjecture, (esk9_0=k1_xboole_0|esk11_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_50])])).
% 0.13/0.39  cnf(c_0_53, negated_conjecture, (k1_relset_1(esk9_0,k1_xboole_0,esk11_0)=k1_relat_1(esk11_0)), inference(rw,[status(thm)],[c_0_27, c_0_47])).
% 0.13/0.39  cnf(c_0_54, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_51])).
% 0.13/0.39  cnf(c_0_55, negated_conjecture, (esk11_0=k1_xboole_0|v1_funct_2(esk11_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_49, c_0_52])).
% 0.13/0.39  cnf(c_0_56, negated_conjecture, (esk11_0=k1_xboole_0|m1_subset_1(esk11_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_50, c_0_52])).
% 0.13/0.39  fof(c_0_57, plain, ![X17]:((k1_relat_1(X17)!=k1_xboole_0|k2_relat_1(X17)=k1_xboole_0|~v1_relat_1(X17))&(k2_relat_1(X17)!=k1_xboole_0|k1_relat_1(X17)=k1_xboole_0|~v1_relat_1(X17))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.13/0.39  cnf(c_0_58, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk11_0)=k1_relat_1(esk11_0)|esk11_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.13/0.39  cnf(c_0_59, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk11_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.13/0.39  cnf(c_0_60, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.39  cnf(c_0_61, negated_conjecture, (k1_relat_1(esk11_0)=k1_xboole_0|esk11_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.39  cnf(c_0_62, negated_conjecture, (k2_relat_1(esk11_0)!=k1_xboole_0), inference(rw,[status(thm)],[c_0_30, c_0_47])).
% 0.13/0.39  cnf(c_0_63, negated_conjecture, (esk11_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_36])]), c_0_62])).
% 0.13/0.39  cnf(c_0_64, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.39  cnf(c_0_65, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_63]), c_0_64])]), ['proof']).
% 0.13/0.39  # SZS output end CNFRefutation
% 0.13/0.39  # Proof object total steps             : 66
% 0.13/0.39  # Proof object clause steps            : 46
% 0.13/0.39  # Proof object formula steps           : 20
% 0.13/0.39  # Proof object conjectures             : 33
% 0.13/0.39  # Proof object clause conjectures      : 30
% 0.13/0.39  # Proof object formula conjectures     : 3
% 0.13/0.39  # Proof object initial clauses used    : 18
% 0.13/0.39  # Proof object initial formulas used   : 10
% 0.13/0.39  # Proof object generating inferences   : 18
% 0.13/0.39  # Proof object simplifying inferences  : 32
% 0.13/0.39  # Training examples: 0 positive, 0 negative
% 0.13/0.39  # Parsed axioms                        : 10
% 0.13/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.39  # Initial clauses                      : 32
% 0.13/0.39  # Removed in clause preprocessing      : 0
% 0.13/0.39  # Initial clauses in saturation        : 32
% 0.13/0.39  # Processed clauses                    : 133
% 0.13/0.39  # ...of these trivial                  : 2
% 0.13/0.39  # ...subsumed                          : 7
% 0.13/0.39  # ...remaining for further processing  : 124
% 0.13/0.39  # Other redundant clauses eliminated   : 11
% 0.13/0.39  # Clauses deleted for lack of memory   : 0
% 0.13/0.39  # Backward-subsumed                    : 0
% 0.13/0.39  # Backward-rewritten                   : 51
% 0.13/0.39  # Generated clauses                    : 138
% 0.13/0.39  # ...of the previous two non-trivial   : 143
% 0.13/0.39  # Contextual simplify-reflections      : 1
% 0.13/0.39  # Paramodulations                      : 129
% 0.13/0.39  # Factorizations                       : 0
% 0.13/0.39  # Equation resolutions                 : 11
% 0.13/0.39  # Propositional unsat checks           : 0
% 0.13/0.39  #    Propositional check models        : 0
% 0.13/0.39  #    Propositional check unsatisfiable : 0
% 0.13/0.39  #    Propositional clauses             : 0
% 0.13/0.39  #    Propositional clauses after purity: 0
% 0.13/0.39  #    Propositional unsat core size     : 0
% 0.13/0.39  #    Propositional preprocessing time  : 0.000
% 0.13/0.39  #    Propositional encoding time       : 0.000
% 0.13/0.39  #    Propositional solver time         : 0.000
% 0.13/0.39  #    Success case prop preproc time    : 0.000
% 0.13/0.39  #    Success case prop encoding time   : 0.000
% 0.13/0.39  #    Success case prop solver time     : 0.000
% 0.13/0.39  # Current number of processed clauses  : 32
% 0.13/0.39  #    Positive orientable unit clauses  : 4
% 0.13/0.39  #    Positive unorientable unit clauses: 0
% 0.13/0.39  #    Negative unit clauses             : 0
% 0.13/0.39  #    Non-unit-clauses                  : 28
% 0.13/0.39  # Current number of unprocessed clauses: 72
% 0.13/0.39  # ...number of literals in the above   : 249
% 0.13/0.39  # Current number of archived formulas  : 0
% 0.13/0.39  # Current number of archived clauses   : 83
% 0.13/0.39  # Clause-clause subsumption calls (NU) : 289
% 0.13/0.39  # Rec. Clause-clause subsumption calls : 163
% 0.13/0.39  # Non-unit clause-clause subsumptions  : 6
% 0.13/0.39  # Unit Clause-clause subsumption calls : 25
% 0.13/0.39  # Rewrite failures with RHS unbound    : 0
% 0.13/0.39  # BW rewrite match attempts            : 3
% 0.13/0.39  # BW rewrite match successes           : 3
% 0.13/0.39  # Condensation attempts                : 0
% 0.13/0.39  # Condensation successes               : 0
% 0.13/0.39  # Termbank termtop insertions          : 5544
% 0.13/0.39  
% 0.13/0.39  # -------------------------------------------------
% 0.13/0.39  # User time                : 0.036 s
% 0.13/0.39  # System time              : 0.004 s
% 0.13/0.39  # Total time               : 0.040 s
% 0.13/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
