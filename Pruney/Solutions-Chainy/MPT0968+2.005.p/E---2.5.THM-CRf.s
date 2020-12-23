%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:01:26 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 726 expanded)
%              Number of clauses        :   33 ( 294 expanded)
%              Number of leaves         :    8 ( 174 expanded)
%              Depth                    :   16
%              Number of atoms          :  196 (3301 expanded)
%              Number of equality atoms :   69 (1066 expanded)
%              Maximal formula depth    :   25 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t11_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(d2_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k1_funct_2(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( v1_relat_1(X5)
              & v1_funct_1(X5)
              & X4 = X5
              & k1_relat_1(X5) = X1
              & r1_tarski(k2_relat_1(X5),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(c_0_8,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t11_funct_2])).

fof(c_0_9,plain,(
    ! [X12,X13,X14] :
      ( ( v4_relat_1(X14,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) )
      & ( v5_relat_1(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_10,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk4_0,esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & ( esk5_0 != k1_xboole_0
      | esk4_0 = k1_xboole_0 )
    & ~ r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).

fof(c_0_11,plain,(
    ! [X8,X9] :
      ( ( ~ v5_relat_1(X9,X8)
        | r1_tarski(k2_relat_1(X9),X8)
        | ~ v1_relat_1(X9) )
      & ( ~ r1_tarski(k2_relat_1(X9),X8)
        | v5_relat_1(X9,X8)
        | ~ v1_relat_1(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_12,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v5_relat_1(esk6_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

fof(c_0_16,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | v1_relat_1(X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_17,plain,(
    ! [X21,X22,X23,X24,X26,X27,X28,X29,X30,X32] :
      ( ( v1_relat_1(esk1_4(X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k1_funct_2(X21,X22) )
      & ( v1_funct_1(esk1_4(X21,X22,X23,X24))
        | ~ r2_hidden(X24,X23)
        | X23 != k1_funct_2(X21,X22) )
      & ( X24 = esk1_4(X21,X22,X23,X24)
        | ~ r2_hidden(X24,X23)
        | X23 != k1_funct_2(X21,X22) )
      & ( k1_relat_1(esk1_4(X21,X22,X23,X24)) = X21
        | ~ r2_hidden(X24,X23)
        | X23 != k1_funct_2(X21,X22) )
      & ( r1_tarski(k2_relat_1(esk1_4(X21,X22,X23,X24)),X22)
        | ~ r2_hidden(X24,X23)
        | X23 != k1_funct_2(X21,X22) )
      & ( ~ v1_relat_1(X27)
        | ~ v1_funct_1(X27)
        | X26 != X27
        | k1_relat_1(X27) != X21
        | ~ r1_tarski(k2_relat_1(X27),X22)
        | r2_hidden(X26,X23)
        | X23 != k1_funct_2(X21,X22) )
      & ( ~ r2_hidden(esk2_3(X28,X29,X30),X30)
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | esk2_3(X28,X29,X30) != X32
        | k1_relat_1(X32) != X28
        | ~ r1_tarski(k2_relat_1(X32),X29)
        | X30 = k1_funct_2(X28,X29) )
      & ( v1_relat_1(esk3_3(X28,X29,X30))
        | r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k1_funct_2(X28,X29) )
      & ( v1_funct_1(esk3_3(X28,X29,X30))
        | r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k1_funct_2(X28,X29) )
      & ( esk2_3(X28,X29,X30) = esk3_3(X28,X29,X30)
        | r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k1_funct_2(X28,X29) )
      & ( k1_relat_1(esk3_3(X28,X29,X30)) = X28
        | r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k1_funct_2(X28,X29) )
      & ( r1_tarski(k2_relat_1(esk3_3(X28,X29,X30)),X29)
        | r2_hidden(esk2_3(X28,X29,X30),X30)
        | X30 = k1_funct_2(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk5_0)
    | ~ v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_21,plain,
    ( r2_hidden(X2,X5)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | X2 != X1
    | k1_relat_1(X1) != X3
    | ~ r1_tarski(k2_relat_1(X1),X4)
    | X5 != k1_funct_2(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk5_0)
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])])).

cnf(c_0_25,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk6_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_13]),c_0_23])])).

cnf(c_0_26,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_27,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))
      | k1_relset_1(X15,X16,X17) = k1_relat_1(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0))
    | ~ v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_29,plain,(
    ! [X18,X19,X20] :
      ( ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X19 = k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X18 = k1_relset_1(X18,X19,X20)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X18 != k1_relset_1(X18,X19,X20)
        | v1_funct_2(X20,X18,X19)
        | X18 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( ~ v1_funct_2(X20,X18,X19)
        | X20 = k1_xboole_0
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) )
      & ( X20 != k1_xboole_0
        | v1_funct_2(X20,X18,X19)
        | X18 = k1_xboole_0
        | X19 != k1_xboole_0
        | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_30,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_19])).

cnf(c_0_32,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( v1_funct_2(esk6_0,esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( k1_relset_1(esk4_0,esk5_0,esk6_0) = k1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_13]),c_0_23])])).

cnf(c_0_36,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk4_0
    | esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_13])])).

cnf(c_0_37,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_38,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk5_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_39,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_40,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | ~ v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38,c_0_39])])).

cnf(c_0_42,plain,
    ( k1_relset_1(k1_xboole_0,X1,X2) = k1_xboole_0
    | ~ v1_funct_2(X2,k1_xboole_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_43,negated_conjecture,
    ( v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_39]),c_0_41])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_39]),c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),k1_xboole_0)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( k1_relat_1(esk6_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_39]),c_0_41]),c_0_45])).

cnf(c_0_48,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_39]),c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_46,c_0_47]),c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 11:39:26 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.34  # No SInE strategy applied
% 0.19/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t11_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.19/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.38  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.19/0.38  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.19/0.38  fof(d2_funct_2, axiom, ![X1, X2, X3]:(X3=k1_funct_2(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((((v1_relat_1(X5)&v1_funct_1(X5))&X4=X5)&k1_relat_1(X5)=X1)&r1_tarski(k2_relat_1(X5),X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 0.19/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.19/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.19/0.38  fof(c_0_8, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2))))), inference(assume_negation,[status(cth)],[t11_funct_2])).
% 0.19/0.38  fof(c_0_9, plain, ![X12, X13, X14]:((v4_relat_1(X14,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))&(v5_relat_1(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X12,X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.38  fof(c_0_10, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk4_0,esk5_0))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&((esk5_0!=k1_xboole_0|esk4_0=k1_xboole_0)&~r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])).
% 0.19/0.38  fof(c_0_11, plain, ![X8, X9]:((~v5_relat_1(X9,X8)|r1_tarski(k2_relat_1(X9),X8)|~v1_relat_1(X9))&(~r1_tarski(k2_relat_1(X9),X8)|v5_relat_1(X9,X8)|~v1_relat_1(X9))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.19/0.38  cnf(c_0_12, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_14, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (v5_relat_1(esk6_0,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.38  fof(c_0_16, plain, ![X6, X7]:(~v1_relat_1(X6)|(~m1_subset_1(X7,k1_zfmisc_1(X6))|v1_relat_1(X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.19/0.38  fof(c_0_17, plain, ![X21, X22, X23, X24, X26, X27, X28, X29, X30, X32]:(((((((v1_relat_1(esk1_4(X21,X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k1_funct_2(X21,X22))&(v1_funct_1(esk1_4(X21,X22,X23,X24))|~r2_hidden(X24,X23)|X23!=k1_funct_2(X21,X22)))&(X24=esk1_4(X21,X22,X23,X24)|~r2_hidden(X24,X23)|X23!=k1_funct_2(X21,X22)))&(k1_relat_1(esk1_4(X21,X22,X23,X24))=X21|~r2_hidden(X24,X23)|X23!=k1_funct_2(X21,X22)))&(r1_tarski(k2_relat_1(esk1_4(X21,X22,X23,X24)),X22)|~r2_hidden(X24,X23)|X23!=k1_funct_2(X21,X22)))&(~v1_relat_1(X27)|~v1_funct_1(X27)|X26!=X27|k1_relat_1(X27)!=X21|~r1_tarski(k2_relat_1(X27),X22)|r2_hidden(X26,X23)|X23!=k1_funct_2(X21,X22)))&((~r2_hidden(esk2_3(X28,X29,X30),X30)|(~v1_relat_1(X32)|~v1_funct_1(X32)|esk2_3(X28,X29,X30)!=X32|k1_relat_1(X32)!=X28|~r1_tarski(k2_relat_1(X32),X29))|X30=k1_funct_2(X28,X29))&(((((v1_relat_1(esk3_3(X28,X29,X30))|r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k1_funct_2(X28,X29))&(v1_funct_1(esk3_3(X28,X29,X30))|r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k1_funct_2(X28,X29)))&(esk2_3(X28,X29,X30)=esk3_3(X28,X29,X30)|r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k1_funct_2(X28,X29)))&(k1_relat_1(esk3_3(X28,X29,X30))=X28|r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k1_funct_2(X28,X29)))&(r1_tarski(k2_relat_1(esk3_3(X28,X29,X30)),X29)|r2_hidden(esk2_3(X28,X29,X30),X30)|X30=k1_funct_2(X28,X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_funct_2])])])])])])).
% 0.19/0.38  cnf(c_0_18, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk5_0)|~v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.38  cnf(c_0_19, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.38  fof(c_0_20, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(X2,X5)|~v1_relat_1(X1)|~v1_funct_1(X1)|X2!=X1|k1_relat_1(X1)!=X3|~r1_tarski(k2_relat_1(X1),X4)|X5!=k1_funct_2(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk5_0)|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.38  cnf(c_0_23, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_24, plain, (r2_hidden(X1,k1_funct_2(k1_relat_1(X1),X2))|~v1_funct_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])])).
% 0.19/0.38  cnf(c_0_25, negated_conjecture, (r1_tarski(k2_relat_1(esk6_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_13]), c_0_23])])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_27, plain, ![X15, X16, X17]:(~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))|k1_relset_1(X15,X16,X17)=k1_relat_1(X17)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0))|~v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.19/0.38  fof(c_0_29, plain, ![X18, X19, X20]:((((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X19=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))&((~v1_funct_2(X20,X18,X19)|X18=k1_relset_1(X18,X19,X20)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X18!=k1_relset_1(X18,X19,X20)|v1_funct_2(X20,X18,X19)|X18!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))))&((~v1_funct_2(X20,X18,X19)|X20=k1_xboole_0|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19))))&(X20!=k1_xboole_0|v1_funct_2(X20,X18,X19)|X18=k1_xboole_0|X19!=k1_xboole_0|~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.19/0.38  cnf(c_0_30, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_28, c_0_19])).
% 0.19/0.38  cnf(c_0_32, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v1_funct_2(esk6_0,esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (k1_relset_1(esk4_0,esk5_0,esk6_0)=k1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_30, c_0_13])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_13]), c_0_23])])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (k1_relat_1(esk6_0)=esk4_0|esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_13])])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (~r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (esk4_0=k1_xboole_0|esk5_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.19/0.38  cnf(c_0_40, plain, (X2=k1_relset_1(X2,X3,X1)|~v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_38, c_0_39])])).
% 0.19/0.38  cnf(c_0_42, plain, (k1_relset_1(k1_xboole_0,X1,X2)=k1_xboole_0|~v1_funct_2(X2,k1_xboole_0,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))), inference(er,[status(thm)],[c_0_40])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (v1_funct_2(esk6_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_39]), c_0_41])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_39]), c_0_41])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (k1_relset_1(k1_xboole_0,k1_xboole_0,esk6_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(esk6_0,k1_funct_2(k1_relat_1(esk6_0),k1_xboole_0))), inference(rw,[status(thm)],[c_0_35, c_0_39])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k1_relat_1(esk6_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_39]), c_0_41]), c_0_45])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (~r2_hidden(esk6_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_39]), c_0_41])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_46, c_0_47]), c_0_48]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 50
% 0.19/0.38  # Proof object clause steps            : 33
% 0.19/0.38  # Proof object formula steps           : 17
% 0.19/0.38  # Proof object conjectures             : 26
% 0.19/0.38  # Proof object clause conjectures      : 23
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 13
% 0.19/0.38  # Proof object initial formulas used   : 8
% 0.19/0.38  # Proof object generating inferences   : 11
% 0.19/0.38  # Proof object simplifying inferences  : 30
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 8
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 30
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 30
% 0.19/0.38  # Processed clauses                    : 93
% 0.19/0.38  # ...of these trivial                  : 2
% 0.19/0.38  # ...subsumed                          : 0
% 0.19/0.38  # ...remaining for further processing  : 91
% 0.19/0.38  # Other redundant clauses eliminated   : 14
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 0
% 0.19/0.38  # Backward-rewritten                   : 15
% 0.19/0.38  # Generated clauses                    : 53
% 0.19/0.38  # ...of the previous two non-trivial   : 55
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 42
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 14
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 35
% 0.19/0.38  #    Positive orientable unit clauses  : 12
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 1
% 0.19/0.38  #    Non-unit-clauses                  : 22
% 0.19/0.38  # Current number of unprocessed clauses: 22
% 0.19/0.38  # ...number of literals in the above   : 48
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 45
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 192
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 92
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.19/0.38  # Unit Clause-clause subsumption calls : 3
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 5
% 0.19/0.38  # BW rewrite match successes           : 5
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 2996
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.003 s
% 0.19/0.38  # Total time               : 0.035 s
% 0.19/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
