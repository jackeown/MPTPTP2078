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
% DateTime   : Thu Dec  3 11:01:47 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 641 expanded)
%              Number of clauses        :   57 ( 260 expanded)
%              Number of leaves         :   13 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  258 (3308 expanded)
%              Number of equality atoms :   94 ( 760 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
         => ( ! [X5] :
                ( r2_hidden(X5,X1)
               => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
           => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t9_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( ( k1_relat_1(X1) = k1_relat_1(X2)
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(redefinition_r2_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_relset_1(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ! [X4] :
            ( ( v1_funct_1(X4)
              & v1_funct_2(X4,X1,X2)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
           => ( ! [X5] :
                  ( r2_hidden(X5,X1)
                 => k1_funct_1(X3,X5) = k1_funct_1(X4,X5) )
             => r2_relset_1(X1,X2,X3,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_2])).

fof(c_0_14,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k1_relset_1(X41,X42,X43) = k1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_15,negated_conjecture,(
    ! [X55] :
      ( v1_funct_1(esk7_0)
      & v1_funct_2(esk7_0,esk5_0,esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk5_0,esk6_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))
      & ( ~ r2_hidden(X55,esk5_0)
        | k1_funct_1(esk7_0,X55) = k1_funct_1(esk8_0,X55) )
      & ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X48,X49,X50] :
      ( ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X49 = k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X48 = k1_relset_1(X48,X49,X50)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X48 != k1_relset_1(X48,X49,X50)
        | v1_funct_2(X50,X48,X49)
        | X48 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( ~ v1_funct_2(X50,X48,X49)
        | X50 = k1_xboole_0
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( X50 != k1_xboole_0
        | v1_funct_2(X50,X48,X49)
        | X48 = k1_xboole_0
        | X49 != k1_xboole_0
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_17,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))
      | v1_relat_1(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_20,plain,(
    ! [X25,X26] :
      ( ( r2_hidden(esk2_2(X25,X26),k1_relat_1(X25))
        | k1_relat_1(X25) != k1_relat_1(X26)
        | X25 = X26
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( k1_funct_1(X25,esk2_2(X25,X26)) != k1_funct_1(X26,esk2_2(X25,X26))
        | k1_relat_1(X25) != k1_relat_1(X26)
        | X25 = X26
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).

cnf(c_0_21,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk8_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_2(esk7_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X20,X21] :
      ( ( ~ m1_subset_1(X20,k1_zfmisc_1(X21))
        | r1_tarski(X20,X21) )
      & ( ~ r1_tarski(X20,X21)
        | m1_subset_1(X20,k1_zfmisc_1(X21)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))
    | X1 = X2
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_22])]),c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_31,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_25]),c_0_26])])).

cnf(c_0_33,negated_conjecture,
    ( k1_relset_1(esk5_0,esk6_0,esk7_0) = k1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_25])).

fof(c_0_34,plain,(
    ! [X19] : m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_35,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X16] :
      ( ~ r1_tarski(X16,k1_xboole_0)
      | X16 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_38,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = X1
    | r2_hidden(esk2_2(esk8_0,X1),esk5_0)
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_39,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk5_0
    | esk6_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_42,plain,(
    ! [X22,X23,X24] :
      ( ~ r2_hidden(X22,X23)
      | ~ m1_subset_1(X23,k1_zfmisc_1(X24))
      | ~ v1_xboole_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_18])).

cnf(c_0_46,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_48,plain,
    ( X1 = X2
    | k1_funct_1(X1,esk2_2(X1,X2)) != k1_funct_1(X2,esk2_2(X1,X2))
    | k1_relat_1(X1) != k1_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_funct_1(esk8_0,X1)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0
    | r2_hidden(esk2_2(esk8_0,esk7_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40]),c_0_41])])).

fof(c_0_51,plain,(
    ! [X17,X18] :
      ( ( k2_zfmisc_1(X17,X18) != k1_xboole_0
        | X17 = k1_xboole_0
        | X18 = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 )
      & ( X18 != k1_xboole_0
        | k2_zfmisc_1(X17,X18) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_subset_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_43])).

fof(c_0_54,plain,(
    ! [X44,X45,X46,X47] :
      ( ( ~ r2_relset_1(X44,X45,X46,X47)
        | X46 = X47
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X46 != X47
        | r2_relset_1(X44,X45,X46,X47)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_25])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_57,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk8_0 = X1
    | k1_funct_1(esk8_0,esk2_2(esk8_0,X1)) != k1_funct_1(X1,esk2_2(esk8_0,X1))
    | k1_relat_1(X1) != esk5_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_29]),c_0_30]),c_0_31])])).

cnf(c_0_59,negated_conjecture,
    ( k1_funct_1(esk8_0,esk2_2(esk8_0,esk7_0)) = k1_funct_1(esk7_0,esk2_2(esk8_0,esk7_0))
    | esk6_0 = k1_xboole_0
    | esk8_0 = esk7_0 ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_60,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_subset_1(X1)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_43])).

cnf(c_0_62,plain,
    ( k2_subset_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_46,c_0_53])).

cnf(c_0_63,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_64,plain,
    ( r2_relset_1(X3,X4,X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_55])).

cnf(c_0_66,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk8_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_67,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk6_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_39]),c_0_40]),c_0_41])]),c_0_59])).

cnf(c_0_68,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_69,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_63])])).

cnf(c_0_70,plain,
    ( r2_relset_1(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_72,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | r2_hidden(esk1_2(esk7_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_57])).

cnf(c_0_73,negated_conjecture,
    ( ~ r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_74,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_25])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | r2_hidden(esk1_2(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_47])).

cnf(c_0_77,negated_conjecture,
    ( esk8_0 = esk7_0
    | esk7_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_67]),c_0_68]),c_0_69])).

cnf(c_0_78,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_79,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( esk7_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,plain,
    ( r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_78]),c_0_80]),c_0_81])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:04:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.42  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.19/0.42  # and selection function SelectNewComplexAHP.
% 0.19/0.42  #
% 0.19/0.42  # Preprocessing time       : 0.029 s
% 0.19/0.42  # Presaturation interreduction done
% 0.19/0.42  
% 0.19/0.42  # Proof found!
% 0.19/0.42  # SZS status Theorem
% 0.19/0.42  # SZS output start CNFRefutation
% 0.19/0.42  fof(t18_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 0.19/0.42  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.42  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.42  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.42  fof(t9_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>((k1_relat_1(X1)=k1_relat_1(X2)&![X3]:(r2_hidden(X3,k1_relat_1(X1))=>k1_funct_1(X1,X3)=k1_funct_1(X2,X3)))=>X1=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 0.19/0.42  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.42  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.42  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.19/0.42  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.42  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.42  fof(redefinition_r2_relset_1, axiom, ![X1, X2, X3, X4]:((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_relset_1(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 0.19/0.42  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.42  fof(c_0_13, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(![X5]:(r2_hidden(X5,X1)=>k1_funct_1(X3,X5)=k1_funct_1(X4,X5))=>r2_relset_1(X1,X2,X3,X4))))), inference(assume_negation,[status(cth)],[t18_funct_2])).
% 0.19/0.42  fof(c_0_14, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k1_relset_1(X41,X42,X43)=k1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.42  fof(c_0_15, negated_conjecture, ![X55]:(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk5_0,esk6_0))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk5_0,esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0))))&((~r2_hidden(X55,esk5_0)|k1_funct_1(esk7_0,X55)=k1_funct_1(esk8_0,X55))&~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])).
% 0.19/0.42  fof(c_0_16, plain, ![X48, X49, X50]:((((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X49=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&((~v1_funct_2(X50,X48,X49)|X48=k1_relset_1(X48,X49,X50)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X48!=k1_relset_1(X48,X49,X50)|v1_funct_2(X50,X48,X49)|X48!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))))&((~v1_funct_2(X50,X48,X49)|X50=k1_xboole_0|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(X50!=k1_xboole_0|v1_funct_2(X50,X48,X49)|X48=k1_xboole_0|X49!=k1_xboole_0|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.42  cnf(c_0_17, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.42  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_19, plain, ![X30, X31, X32]:(~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))|v1_relat_1(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.42  fof(c_0_20, plain, ![X25, X26]:((r2_hidden(esk2_2(X25,X26),k1_relat_1(X25))|k1_relat_1(X25)!=k1_relat_1(X26)|X25=X26|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(k1_funct_1(X25,esk2_2(X25,X26))!=k1_funct_1(X26,esk2_2(X25,X26))|k1_relat_1(X25)!=k1_relat_1(X26)|X25=X26|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_1])])])])])).
% 0.19/0.42  cnf(c_0_21, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.42  cnf(c_0_22, negated_conjecture, (v1_funct_2(esk8_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_23, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.42  cnf(c_0_24, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.42  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk5_0,esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_26, negated_conjecture, (v1_funct_2(esk7_0,esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  fof(c_0_27, plain, ![X20, X21]:((~m1_subset_1(X20,k1_zfmisc_1(X21))|r1_tarski(X20,X21))&(~r1_tarski(X20,X21)|m1_subset_1(X20,k1_zfmisc_1(X21)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.42  cnf(c_0_28, plain, (r2_hidden(esk2_2(X1,X2),k1_relat_1(X1))|X1=X2|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_29, negated_conjecture, (k1_relat_1(esk8_0)=esk5_0|esk6_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_22])]), c_0_23])).
% 0.19/0.42  cnf(c_0_30, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_31, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_24, c_0_18])).
% 0.19/0.42  cnf(c_0_32, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_25]), c_0_26])])).
% 0.19/0.42  cnf(c_0_33, negated_conjecture, (k1_relset_1(esk5_0,esk6_0,esk7_0)=k1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_17, c_0_25])).
% 0.19/0.42  fof(c_0_34, plain, ![X19]:m1_subset_1(k2_subset_1(X19),k1_zfmisc_1(X19)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.42  fof(c_0_35, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.42  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  fof(c_0_37, plain, ![X16]:(~r1_tarski(X16,k1_xboole_0)|X16=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.19/0.42  cnf(c_0_38, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=X1|r2_hidden(esk2_2(esk8_0,X1),esk5_0)|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_30]), c_0_31])])).
% 0.19/0.42  cnf(c_0_39, negated_conjecture, (k1_relat_1(esk7_0)=esk5_0|esk6_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.42  cnf(c_0_40, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_41, negated_conjecture, (v1_relat_1(esk7_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.42  fof(c_0_42, plain, ![X22, X23, X24]:(~r2_hidden(X22,X23)|~m1_subset_1(X23,k1_zfmisc_1(X24))|~v1_xboole_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.42  cnf(c_0_43, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.42  cnf(c_0_44, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_45, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_36, c_0_18])).
% 0.19/0.42  cnf(c_0_46, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.42  cnf(c_0_47, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.42  cnf(c_0_48, plain, (X1=X2|k1_funct_1(X1,esk2_2(X1,X2))!=k1_funct_1(X2,esk2_2(X1,X2))|k1_relat_1(X1)!=k1_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.42  cnf(c_0_49, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_funct_1(esk8_0,X1)|~r2_hidden(X1,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_50, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0|r2_hidden(esk2_2(esk8_0,esk7_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40]), c_0_41])])).
% 0.19/0.42  fof(c_0_51, plain, ![X17, X18]:((k2_zfmisc_1(X17,X18)!=k1_xboole_0|(X17=k1_xboole_0|X18=k1_xboole_0))&((X17!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0)&(X18!=k1_xboole_0|k2_zfmisc_1(X17,X18)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.42  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.42  cnf(c_0_53, plain, (r1_tarski(k2_subset_1(X1),X1)), inference(spm,[status(thm)],[c_0_36, c_0_43])).
% 0.19/0.42  fof(c_0_54, plain, ![X44, X45, X46, X47]:((~r2_relset_1(X44,X45,X46,X47)|X46=X47|(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(X46!=X47|r2_relset_1(X44,X45,X46,X47)|(~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_relset_1])])])).
% 0.19/0.42  cnf(c_0_55, negated_conjecture, (r1_tarski(esk7_0,k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_36, c_0_25])).
% 0.19/0.42  cnf(c_0_56, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.42  cnf(c_0_57, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.42  cnf(c_0_58, negated_conjecture, (esk6_0=k1_xboole_0|esk8_0=X1|k1_funct_1(esk8_0,esk2_2(esk8_0,X1))!=k1_funct_1(X1,esk2_2(esk8_0,X1))|k1_relat_1(X1)!=esk5_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_29]), c_0_30]), c_0_31])])).
% 0.19/0.42  cnf(c_0_59, negated_conjecture, (k1_funct_1(esk8_0,esk2_2(esk8_0,esk7_0))=k1_funct_1(esk7_0,esk2_2(esk8_0,esk7_0))|esk6_0=k1_xboole_0|esk8_0=esk7_0), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.42  cnf(c_0_60, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.19/0.42  cnf(c_0_61, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k2_subset_1(X1))), inference(spm,[status(thm)],[c_0_52, c_0_43])).
% 0.19/0.42  cnf(c_0_62, plain, (k2_subset_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_46, c_0_53])).
% 0.19/0.42  cnf(c_0_63, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.42  cnf(c_0_64, plain, (r2_relset_1(X3,X4,X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.42  cnf(c_0_65, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk5_0,esk6_0))|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_44, c_0_55])).
% 0.19/0.42  cnf(c_0_66, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk1_2(esk8_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.42  cnf(c_0_67, negated_conjecture, (esk8_0=esk7_0|esk6_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_39]), c_0_40]), c_0_41])]), c_0_59])).
% 0.19/0.42  cnf(c_0_68, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_60])).
% 0.19/0.42  cnf(c_0_69, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_63])])).
% 0.19/0.42  cnf(c_0_70, plain, (r2_relset_1(X1,X2,X3,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(er,[status(thm)],[c_0_64])).
% 0.19/0.42  cnf(c_0_71, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.42  cnf(c_0_72, negated_conjecture, (esk7_0=k1_xboole_0|r2_hidden(esk1_2(esk7_0,k1_xboole_0),k2_zfmisc_1(esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_57])).
% 0.19/0.42  cnf(c_0_73, negated_conjecture, (~r2_relset_1(esk5_0,esk6_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.42  cnf(c_0_74, negated_conjecture, (esk8_0=esk7_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68]), c_0_69])).
% 0.19/0.42  cnf(c_0_75, negated_conjecture, (r2_relset_1(esk5_0,esk6_0,esk7_0,esk7_0)), inference(spm,[status(thm)],[c_0_70, c_0_25])).
% 0.19/0.42  cnf(c_0_76, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|r2_hidden(esk1_2(X1,X2),X1)), inference(spm,[status(thm)],[c_0_71, c_0_47])).
% 0.19/0.42  cnf(c_0_77, negated_conjecture, (esk8_0=esk7_0|esk7_0=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_67]), c_0_68]), c_0_69])).
% 0.19/0.42  cnf(c_0_78, negated_conjecture, (esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])])).
% 0.19/0.42  cnf(c_0_79, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_69, c_0_76])).
% 0.19/0.42  cnf(c_0_80, negated_conjecture, (esk7_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.19/0.42  cnf(c_0_81, plain, (r2_relset_1(X1,X2,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_70, c_0_79])).
% 0.19/0.42  cnf(c_0_82, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_78]), c_0_80]), c_0_81])]), ['proof']).
% 0.19/0.42  # SZS output end CNFRefutation
% 0.19/0.42  # Proof object total steps             : 83
% 0.19/0.42  # Proof object clause steps            : 57
% 0.19/0.42  # Proof object formula steps           : 26
% 0.19/0.42  # Proof object conjectures             : 35
% 0.19/0.42  # Proof object clause conjectures      : 32
% 0.19/0.42  # Proof object formula conjectures     : 3
% 0.19/0.42  # Proof object initial clauses used    : 23
% 0.19/0.42  # Proof object initial formulas used   : 13
% 0.19/0.42  # Proof object generating inferences   : 31
% 0.19/0.42  # Proof object simplifying inferences  : 32
% 0.19/0.42  # Training examples: 0 positive, 0 negative
% 0.19/0.42  # Parsed axioms                        : 16
% 0.19/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.42  # Initial clauses                      : 40
% 0.19/0.42  # Removed in clause preprocessing      : 0
% 0.19/0.42  # Initial clauses in saturation        : 40
% 0.19/0.42  # Processed clauses                    : 516
% 0.19/0.42  # ...of these trivial                  : 8
% 0.19/0.42  # ...subsumed                          : 121
% 0.19/0.42  # ...remaining for further processing  : 386
% 0.19/0.42  # Other redundant clauses eliminated   : 9
% 0.19/0.42  # Clauses deleted for lack of memory   : 0
% 0.19/0.42  # Backward-subsumed                    : 9
% 0.19/0.42  # Backward-rewritten                   : 198
% 0.19/0.42  # Generated clauses                    : 1535
% 0.19/0.42  # ...of the previous two non-trivial   : 1449
% 0.19/0.42  # Contextual simplify-reflections      : 3
% 0.19/0.42  # Paramodulations                      : 1524
% 0.19/0.42  # Factorizations                       : 1
% 0.19/0.42  # Equation resolutions                 : 11
% 0.19/0.42  # Propositional unsat checks           : 0
% 0.19/0.42  #    Propositional check models        : 0
% 0.19/0.42  #    Propositional check unsatisfiable : 0
% 0.19/0.42  #    Propositional clauses             : 0
% 0.19/0.42  #    Propositional clauses after purity: 0
% 0.19/0.42  #    Propositional unsat core size     : 0
% 0.19/0.42  #    Propositional preprocessing time  : 0.000
% 0.19/0.42  #    Propositional encoding time       : 0.000
% 0.19/0.42  #    Propositional solver time         : 0.000
% 0.19/0.42  #    Success case prop preproc time    : 0.000
% 0.19/0.42  #    Success case prop encoding time   : 0.000
% 0.19/0.42  #    Success case prop solver time     : 0.000
% 0.19/0.42  # Current number of processed clauses  : 132
% 0.19/0.42  #    Positive orientable unit clauses  : 25
% 0.19/0.42  #    Positive unorientable unit clauses: 0
% 0.19/0.42  #    Negative unit clauses             : 1
% 0.19/0.42  #    Non-unit-clauses                  : 106
% 0.19/0.42  # Current number of unprocessed clauses: 1008
% 0.19/0.42  # ...number of literals in the above   : 2724
% 0.19/0.42  # Current number of archived formulas  : 0
% 0.19/0.42  # Current number of archived clauses   : 247
% 0.19/0.42  # Clause-clause subsumption calls (NU) : 9103
% 0.19/0.42  # Rec. Clause-clause subsumption calls : 5577
% 0.19/0.42  # Non-unit clause-clause subsumptions  : 126
% 0.19/0.42  # Unit Clause-clause subsumption calls : 961
% 0.19/0.42  # Rewrite failures with RHS unbound    : 0
% 0.19/0.42  # BW rewrite match attempts            : 176
% 0.19/0.42  # BW rewrite match successes           : 12
% 0.19/0.42  # Condensation attempts                : 0
% 0.19/0.42  # Condensation successes               : 0
% 0.19/0.42  # Termbank termtop insertions          : 29947
% 0.19/0.42  
% 0.19/0.42  # -------------------------------------------------
% 0.19/0.42  # User time                : 0.071 s
% 0.19/0.42  # System time              : 0.005 s
% 0.19/0.42  # Total time               : 0.076 s
% 0.19/0.42  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
