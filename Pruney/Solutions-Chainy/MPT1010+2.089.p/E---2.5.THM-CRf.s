%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:24 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  101 (1709 expanded)
%              Number of clauses        :   68 ( 718 expanded)
%              Number of leaves         :   16 ( 465 expanded)
%              Depth                    :   28
%              Number of atoms          :  320 (4380 expanded)
%              Number of equality atoms :  128 (2052 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

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

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t12_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_17,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X39,X40] :
      ( ( ~ v5_relat_1(X40,X39)
        | r1_tarski(k2_relat_1(X40),X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r1_tarski(k2_relat_1(X40),X39)
        | v5_relat_1(X40,X39)
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_19,plain,(
    ! [X24,X25,X26,X27,X28,X29] :
      ( ( ~ r2_hidden(X26,X25)
        | X26 = X24
        | X25 != k1_tarski(X24) )
      & ( X27 != X24
        | r2_hidden(X27,X25)
        | X25 != k1_tarski(X24) )
      & ( ~ r2_hidden(esk3_2(X28,X29),X29)
        | esk3_2(X28,X29) != X28
        | X29 = k1_tarski(X28) )
      & ( r2_hidden(esk3_2(X28,X29),X29)
        | esk3_2(X28,X29) = X28
        | X29 = k1_tarski(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X31] : k2_tarski(X31,X31) = k1_tarski(X31) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_21,plain,(
    ! [X32,X33] : k1_enumset1(X32,X32,X33) = k2_tarski(X32,X33) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_22,plain,(
    ! [X34,X35,X36] : k2_enumset1(X34,X34,X35,X36) = k1_enumset1(X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_23,negated_conjecture,
    ( v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))
    & r2_hidden(esk6_0,esk4_0)
    & k1_funct_1(esk7_0,esk6_0) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_24,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X47,X48,X49] :
      ( ( v4_relat_1(X49,X47)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) )
      & ( v5_relat_1(X49,X48)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X37,X38] :
      ( ~ v1_relat_1(X37)
      | ~ m1_subset_1(X38,k1_zfmisc_1(X37))
      | v1_relat_1(X38) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_33,plain,(
    ! [X41,X42] : v1_relat_1(k2_zfmisc_1(X41,X42)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_34,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_36,plain,
    ( esk3_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk3_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_37,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_39,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_42,plain,
    ( k2_relat_1(X1) = k2_enumset1(X2,X2,X2,X2)
    | esk3_2(X2,k2_relat_1(X1)) = X2
    | r2_hidden(esk3_2(X2,k2_relat_1(X1)),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( v5_relat_1(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_38]),c_0_40])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | esk3_2(X1,k2_relat_1(esk7_0)) = X1
    | r2_hidden(esk3_2(X1,k2_relat_1(esk7_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])])).

cnf(c_0_47,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | esk3_2(X1,k2_relat_1(esk7_0)) = esk5_0
    | esk3_2(X1,k2_relat_1(esk7_0)) = X1 ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_49,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk3_2(X1,X2) != X1
    | ~ r2_hidden(esk3_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_50,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k2_relat_1(esk7_0)
    | esk3_2(esk5_0,k2_relat_1(esk7_0)) = esk5_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_48])])).

fof(c_0_51,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X17,X16)
        | X17 = X13
        | X17 = X14
        | X17 = X15
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X13
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X14
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( X18 != X15
        | r2_hidden(X18,X16)
        | X16 != k1_enumset1(X13,X14,X15) )
      & ( esk2_4(X19,X20,X21,X22) != X19
        | ~ r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X19,X20,X21,X22) != X20
        | ~ r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( esk2_4(X19,X20,X21,X22) != X21
        | ~ r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | X22 = k1_enumset1(X19,X20,X21) )
      & ( r2_hidden(esk2_4(X19,X20,X21,X22),X22)
        | esk2_4(X19,X20,X21,X22) = X19
        | esk2_4(X19,X20,X21,X22) = X20
        | esk2_4(X19,X20,X21,X22) = X21
        | X22 = k1_enumset1(X19,X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_52,plain,(
    ! [X50,X51,X52] :
      ( ~ m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))
      | k1_relset_1(X50,X51,X52) = k1_relat_1(X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_53,plain,(
    ! [X53,X54,X55] :
      ( ( ~ v1_funct_2(X55,X53,X54)
        | X53 = k1_relset_1(X53,X54,X55)
        | X54 = k1_xboole_0
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( X53 != k1_relset_1(X53,X54,X55)
        | v1_funct_2(X55,X53,X54)
        | X54 = k1_xboole_0
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( ~ v1_funct_2(X55,X53,X54)
        | X53 = k1_relset_1(X53,X54,X55)
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( X53 != k1_relset_1(X53,X54,X55)
        | v1_funct_2(X55,X53,X54)
        | X53 != k1_xboole_0
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( ~ v1_funct_2(X55,X53,X54)
        | X55 = k1_xboole_0
        | X53 = k1_xboole_0
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) )
      & ( X55 != k1_xboole_0
        | v1_funct_2(X55,X53,X54)
        | X53 = k1_xboole_0
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_54,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k2_relat_1(esk7_0)
    | ~ r2_hidden(esk5_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_59,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | ~ r1_tarski(X46,X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_60,plain,(
    ! [X12] : r1_tarski(k1_xboole_0,X12) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_61,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | esk3_2(X1,k2_relat_1(esk7_0)) = X1
    | esk5_0 = X1
    | r2_hidden(esk5_0,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_48])).

cnf(c_0_62,negated_conjecture,
    ( X1 = esk5_0
    | ~ r2_hidden(esk5_0,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_54])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_55,c_0_29])).

cnf(c_0_64,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_65,negated_conjecture,
    ( v1_funct_2(esk7_0,esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_66,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk7_0)
    | esk5_0 = X1
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_61]),c_0_62])).

fof(c_0_69,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ v1_funct_1(X44)
      | ~ r2_hidden(X43,k1_relat_1(X44))
      | r2_hidden(k1_funct_1(X44,X43),k2_relat_1(X44)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_63])])).

cnf(c_0_71,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) = k1_xboole_0
    | k1_relat_1(esk7_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_38]),c_0_65])])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( esk5_0 = X1
    | X2 = X1
    | ~ r2_hidden(X2,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_68])).

cnf(c_0_74,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_76,negated_conjecture,
    ( k1_relat_1(esk7_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])).

cnf(c_0_77,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_78,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = X2
    | esk5_0 = X2
    | ~ r2_hidden(X2,k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75]),c_0_44]),c_0_76])])).

cnf(c_0_79,plain,
    ( esk1_2(k2_enumset1(X1,X1,X1,X1),X2) = X1
    | r1_tarski(k2_enumset1(X1,X1,X1,X1),X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_81,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_funct_1(esk7_0,X2)
    | k1_funct_1(esk7_0,X2) = esk5_0
    | ~ r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_74]),c_0_75]),c_0_44]),c_0_76])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_83,negated_conjecture,
    ( esk1_2(k2_relat_1(esk7_0),X1) = X2
    | esk5_0 = X2
    | r1_tarski(k2_relat_1(esk7_0),X1)
    | ~ r2_hidden(X2,k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_68])).

cnf(c_0_84,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) != esk5_0
    | ~ r2_hidden(X1,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])]),c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( esk1_2(k2_relat_1(esk7_0),X1) = k1_funct_1(esk7_0,X2)
    | r1_tarski(k2_relat_1(esk7_0),X1)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_74]),c_0_75]),c_0_44]),c_0_76])]),c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_funct_1(esk7_0,X2)
    | r1_tarski(k2_relat_1(esk7_0),X3)
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_85])).

cnf(c_0_87,negated_conjecture,
    ( k1_funct_1(esk7_0,X1) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(k2_relat_1(esk7_0),X2)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_86,c_0_82])).

cnf(c_0_88,plain,
    ( ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_66,c_0_25])).

cnf(c_0_89,plain,
    ( v5_relat_1(X1,X2)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_90,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk4_0,X1)) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(k2_relat_1(esk7_0),X2)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_87,c_0_77])).

cnf(c_0_91,plain,
    ( ~ v1_funct_1(X1)
    | ~ v5_relat_1(X1,k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_74])).

cnf(c_0_92,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk4_0,X1)) = k1_funct_1(esk7_0,esk6_0)
    | v5_relat_1(esk7_0,X2)
    | r1_tarski(esk4_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_44])])).

cnf(c_0_93,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk4_0,X1)) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(esk4_0,X1)
    | ~ r2_hidden(X2,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_75]),c_0_44]),c_0_76])])).

cnf(c_0_94,negated_conjecture,
    ( k1_funct_1(esk7_0,esk1_2(esk4_0,X1)) = k1_funct_1(esk7_0,esk6_0)
    | r1_tarski(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_93,c_0_82])).

cnf(c_0_95,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))
    | r1_tarski(esk4_0,X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_94]),c_0_75]),c_0_44]),c_0_76])]),c_0_77])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_82])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,esk6_0),X1)
    | ~ v5_relat_1(esk7_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_97]),c_0_44])])).

cnf(c_0_99,negated_conjecture,
    ( k1_funct_1(esk7_0,esk6_0) = X1
    | ~ v5_relat_1(esk7_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_98])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_43]),c_0_80]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.53/0.70  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.53/0.70  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.53/0.70  #
% 0.53/0.70  # Preprocessing time       : 0.041 s
% 0.53/0.70  
% 0.53/0.70  # Proof found!
% 0.53/0.70  # SZS status Theorem
% 0.53/0.70  # SZS output start CNFRefutation
% 0.53/0.70  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.53/0.70  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.53/0.70  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.53/0.70  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.53/0.70  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.53/0.70  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.53/0.70  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.53/0.70  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.53/0.70  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.53/0.70  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.53/0.70  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.53/0.70  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.53/0.70  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.53/0.70  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.53/0.70  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.53/0.70  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.53/0.70  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.53/0.70  fof(c_0_17, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.53/0.70  fof(c_0_18, plain, ![X39, X40]:((~v5_relat_1(X40,X39)|r1_tarski(k2_relat_1(X40),X39)|~v1_relat_1(X40))&(~r1_tarski(k2_relat_1(X40),X39)|v5_relat_1(X40,X39)|~v1_relat_1(X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.53/0.70  fof(c_0_19, plain, ![X24, X25, X26, X27, X28, X29]:(((~r2_hidden(X26,X25)|X26=X24|X25!=k1_tarski(X24))&(X27!=X24|r2_hidden(X27,X25)|X25!=k1_tarski(X24)))&((~r2_hidden(esk3_2(X28,X29),X29)|esk3_2(X28,X29)!=X28|X29=k1_tarski(X28))&(r2_hidden(esk3_2(X28,X29),X29)|esk3_2(X28,X29)=X28|X29=k1_tarski(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.53/0.70  fof(c_0_20, plain, ![X31]:k2_tarski(X31,X31)=k1_tarski(X31), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.53/0.70  fof(c_0_21, plain, ![X32, X33]:k1_enumset1(X32,X32,X33)=k2_tarski(X32,X33), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.53/0.70  fof(c_0_22, plain, ![X34, X35, X36]:k2_enumset1(X34,X34,X35,X36)=k1_enumset1(X34,X35,X36), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.53/0.70  fof(c_0_23, negated_conjecture, (((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0)))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0)))))&(r2_hidden(esk6_0,esk4_0)&k1_funct_1(esk7_0,esk6_0)!=esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.53/0.70  cnf(c_0_24, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.53/0.70  cnf(c_0_25, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.70  cnf(c_0_26, plain, (r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.70  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.70  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.70  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.53/0.70  fof(c_0_30, plain, ![X47, X48, X49]:((v4_relat_1(X49,X47)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))&(v5_relat_1(X49,X48)|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X47,X48))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.53/0.70  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_tarski(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.70  fof(c_0_32, plain, ![X37, X38]:(~v1_relat_1(X37)|(~m1_subset_1(X38,k1_zfmisc_1(X37))|v1_relat_1(X38))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.53/0.70  fof(c_0_33, plain, ![X41, X42]:v1_relat_1(k2_zfmisc_1(X41,X42)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.53/0.70  cnf(c_0_34, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.70  cnf(c_0_35, plain, (r2_hidden(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.53/0.70  cnf(c_0_36, plain, (esk3_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk3_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.53/0.70  cnf(c_0_37, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.70  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_27]), c_0_28]), c_0_29])).
% 0.53/0.70  cnf(c_0_39, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.70  cnf(c_0_40, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.70  cnf(c_0_41, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_27]), c_0_28]), c_0_29])).
% 0.53/0.70  cnf(c_0_42, plain, (k2_relat_1(X1)=k2_enumset1(X2,X2,X2,X2)|esk3_2(X2,k2_relat_1(X1))=X2|r2_hidden(esk3_2(X2,k2_relat_1(X1)),X3)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.53/0.70  cnf(c_0_43, negated_conjecture, (v5_relat_1(esk7_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.53/0.70  cnf(c_0_44, negated_conjecture, (v1_relat_1(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_38]), c_0_40])])).
% 0.53/0.70  cnf(c_0_45, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_41])).
% 0.53/0.70  cnf(c_0_46, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk7_0)|esk3_2(X1,k2_relat_1(esk7_0))=X1|r2_hidden(esk3_2(X1,k2_relat_1(esk7_0)),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])])).
% 0.53/0.70  cnf(c_0_47, plain, (X2=k1_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.70  cnf(c_0_48, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk7_0)|esk3_2(X1,k2_relat_1(esk7_0))=esk5_0|esk3_2(X1,k2_relat_1(esk7_0))=X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.53/0.70  cnf(c_0_49, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk3_2(X1,X2)!=X1|~r2_hidden(esk3_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_27]), c_0_28]), c_0_29])).
% 0.53/0.70  cnf(c_0_50, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k2_relat_1(esk7_0)|esk3_2(esk5_0,k2_relat_1(esk7_0))=esk5_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_48])])).
% 0.53/0.70  fof(c_0_51, plain, ![X13, X14, X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X17,X16)|(X17=X13|X17=X14|X17=X15)|X16!=k1_enumset1(X13,X14,X15))&(((X18!=X13|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))&(X18!=X14|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15)))&(X18!=X15|r2_hidden(X18,X16)|X16!=k1_enumset1(X13,X14,X15))))&((((esk2_4(X19,X20,X21,X22)!=X19|~r2_hidden(esk2_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21))&(esk2_4(X19,X20,X21,X22)!=X20|~r2_hidden(esk2_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(esk2_4(X19,X20,X21,X22)!=X21|~r2_hidden(esk2_4(X19,X20,X21,X22),X22)|X22=k1_enumset1(X19,X20,X21)))&(r2_hidden(esk2_4(X19,X20,X21,X22),X22)|(esk2_4(X19,X20,X21,X22)=X19|esk2_4(X19,X20,X21,X22)=X20|esk2_4(X19,X20,X21,X22)=X21)|X22=k1_enumset1(X19,X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.53/0.70  fof(c_0_52, plain, ![X50, X51, X52]:(~m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(X50,X51)))|k1_relset_1(X50,X51,X52)=k1_relat_1(X52)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.53/0.70  fof(c_0_53, plain, ![X53, X54, X55]:((((~v1_funct_2(X55,X53,X54)|X53=k1_relset_1(X53,X54,X55)|X54=k1_xboole_0|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(X53!=k1_relset_1(X53,X54,X55)|v1_funct_2(X55,X53,X54)|X54=k1_xboole_0|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))))&((~v1_funct_2(X55,X53,X54)|X53=k1_relset_1(X53,X54,X55)|X53!=k1_xboole_0|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(X53!=k1_relset_1(X53,X54,X55)|v1_funct_2(X55,X53,X54)|X53!=k1_xboole_0|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))))&((~v1_funct_2(X55,X53,X54)|X55=k1_xboole_0|X53=k1_xboole_0|X54!=k1_xboole_0|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54))))&(X55!=k1_xboole_0|v1_funct_2(X55,X53,X54)|X53=k1_xboole_0|X54!=k1_xboole_0|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X53,X54)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.53/0.70  cnf(c_0_54, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k2_relat_1(esk7_0)|~r2_hidden(esk5_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.53/0.70  cnf(c_0_55, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.53/0.70  cnf(c_0_56, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.53/0.70  cnf(c_0_57, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.53/0.70  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k1_tarski(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.70  fof(c_0_59, plain, ![X45, X46]:(~r2_hidden(X45,X46)|~r1_tarski(X46,X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.53/0.70  fof(c_0_60, plain, ![X12]:r1_tarski(k1_xboole_0,X12), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.53/0.70  cnf(c_0_61, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk7_0)|esk3_2(X1,k2_relat_1(esk7_0))=X1|esk5_0=X1|r2_hidden(esk5_0,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_36, c_0_48])).
% 0.53/0.70  cnf(c_0_62, negated_conjecture, (X1=esk5_0|~r2_hidden(esk5_0,k2_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_54])).
% 0.53/0.70  cnf(c_0_63, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_55, c_0_29])).
% 0.53/0.70  cnf(c_0_64, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.53/0.70  cnf(c_0_65, negated_conjecture, (v1_funct_2(esk7_0,esk4_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_27]), c_0_28]), c_0_29])).
% 0.53/0.70  cnf(c_0_66, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.53/0.70  cnf(c_0_67, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.53/0.70  cnf(c_0_68, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk7_0)|esk5_0=X1|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_61]), c_0_62])).
% 0.53/0.70  fof(c_0_69, plain, ![X43, X44]:(~v1_relat_1(X44)|~v1_funct_1(X44)|(~r2_hidden(X43,k1_relat_1(X44))|r2_hidden(k1_funct_1(X44,X43),k2_relat_1(X44)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.53/0.70  cnf(c_0_70, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_63])])).
% 0.53/0.70  cnf(c_0_71, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)=k1_xboole_0|k1_relat_1(esk7_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_38]), c_0_65])])).
% 0.53/0.70  cnf(c_0_72, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.53/0.70  cnf(c_0_73, negated_conjecture, (esk5_0=X1|X2=X1|~r2_hidden(X2,k2_relat_1(esk7_0))|~r2_hidden(X1,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_45, c_0_68])).
% 0.53/0.70  cnf(c_0_74, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.53/0.70  cnf(c_0_75, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.70  cnf(c_0_76, negated_conjecture, (k1_relat_1(esk7_0)=esk4_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_72])).
% 0.53/0.70  cnf(c_0_77, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.53/0.70  cnf(c_0_78, negated_conjecture, (k1_funct_1(esk7_0,X1)=X2|esk5_0=X2|~r2_hidden(X2,k2_relat_1(esk7_0))|~r2_hidden(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75]), c_0_44]), c_0_76])])).
% 0.53/0.70  cnf(c_0_79, plain, (esk1_2(k2_enumset1(X1,X1,X1,X1),X2)=X1|r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)), inference(spm,[status(thm)],[c_0_45, c_0_77])).
% 0.53/0.70  cnf(c_0_80, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.70  cnf(c_0_81, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_funct_1(esk7_0,X2)|k1_funct_1(esk7_0,X2)=esk5_0|~r2_hidden(X1,esk4_0)|~r2_hidden(X2,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_74]), c_0_75]), c_0_44]), c_0_76])])).
% 0.53/0.70  cnf(c_0_82, negated_conjecture, (r2_hidden(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.53/0.70  cnf(c_0_83, negated_conjecture, (esk1_2(k2_relat_1(esk7_0),X1)=X2|esk5_0=X2|r1_tarski(k2_relat_1(esk7_0),X1)|~r2_hidden(X2,k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_79, c_0_68])).
% 0.53/0.70  cnf(c_0_84, negated_conjecture, (k1_funct_1(esk7_0,X1)!=esk5_0|~r2_hidden(X1,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])]), c_0_80])).
% 0.53/0.70  cnf(c_0_85, negated_conjecture, (esk1_2(k2_relat_1(esk7_0),X1)=k1_funct_1(esk7_0,X2)|r1_tarski(k2_relat_1(esk7_0),X1)|~r2_hidden(X2,esk4_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_74]), c_0_75]), c_0_44]), c_0_76])]), c_0_84])).
% 0.53/0.70  cnf(c_0_86, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_funct_1(esk7_0,X2)|r1_tarski(k2_relat_1(esk7_0),X3)|~r2_hidden(X2,esk4_0)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_85, c_0_85])).
% 0.53/0.70  cnf(c_0_87, negated_conjecture, (k1_funct_1(esk7_0,X1)=k1_funct_1(esk7_0,esk6_0)|r1_tarski(k2_relat_1(esk7_0),X2)|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_86, c_0_82])).
% 0.53/0.70  cnf(c_0_88, plain, (~v5_relat_1(X1,X2)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(spm,[status(thm)],[c_0_66, c_0_25])).
% 0.53/0.70  cnf(c_0_89, plain, (v5_relat_1(X1,X2)|~r1_tarski(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.70  cnf(c_0_90, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk4_0,X1))=k1_funct_1(esk7_0,esk6_0)|r1_tarski(k2_relat_1(esk7_0),X2)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_87, c_0_77])).
% 0.53/0.70  cnf(c_0_91, plain, (~v1_funct_1(X1)|~v5_relat_1(X1,k1_funct_1(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(spm,[status(thm)],[c_0_88, c_0_74])).
% 0.53/0.70  cnf(c_0_92, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk4_0,X1))=k1_funct_1(esk7_0,esk6_0)|v5_relat_1(esk7_0,X2)|r1_tarski(esk4_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_44])])).
% 0.53/0.70  cnf(c_0_93, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk4_0,X1))=k1_funct_1(esk7_0,esk6_0)|r1_tarski(esk4_0,X1)|~r2_hidden(X2,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_75]), c_0_44]), c_0_76])])).
% 0.53/0.70  cnf(c_0_94, negated_conjecture, (k1_funct_1(esk7_0,esk1_2(esk4_0,X1))=k1_funct_1(esk7_0,esk6_0)|r1_tarski(esk4_0,X1)), inference(spm,[status(thm)],[c_0_93, c_0_82])).
% 0.53/0.70  cnf(c_0_95, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))|r1_tarski(esk4_0,X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_94]), c_0_75]), c_0_44]), c_0_76])]), c_0_77])).
% 0.53/0.70  cnf(c_0_96, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_66, c_0_95])).
% 0.53/0.70  cnf(c_0_97, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),k2_relat_1(esk7_0))), inference(spm,[status(thm)],[c_0_96, c_0_82])).
% 0.53/0.70  cnf(c_0_98, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,esk6_0),X1)|~v5_relat_1(esk7_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_97]), c_0_44])])).
% 0.53/0.70  cnf(c_0_99, negated_conjecture, (k1_funct_1(esk7_0,esk6_0)=X1|~v5_relat_1(esk7_0,k2_enumset1(X1,X1,X1,X1))), inference(spm,[status(thm)],[c_0_45, c_0_98])).
% 0.53/0.70  cnf(c_0_100, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_43]), c_0_80]), ['proof']).
% 0.53/0.70  # SZS output end CNFRefutation
% 0.53/0.70  # Proof object total steps             : 101
% 0.53/0.70  # Proof object clause steps            : 68
% 0.53/0.70  # Proof object formula steps           : 33
% 0.53/0.70  # Proof object conjectures             : 39
% 0.53/0.70  # Proof object clause conjectures      : 36
% 0.53/0.70  # Proof object formula conjectures     : 3
% 0.53/0.70  # Proof object initial clauses used    : 24
% 0.53/0.70  # Proof object initial formulas used   : 16
% 0.53/0.70  # Proof object generating inferences   : 36
% 0.53/0.70  # Proof object simplifying inferences  : 58
% 0.53/0.70  # Training examples: 0 positive, 0 negative
% 0.53/0.70  # Parsed axioms                        : 16
% 0.53/0.70  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.70  # Initial clauses                      : 39
% 0.53/0.70  # Removed in clause preprocessing      : 3
% 0.53/0.70  # Initial clauses in saturation        : 36
% 0.53/0.70  # Processed clauses                    : 999
% 0.53/0.70  # ...of these trivial                  : 11
% 0.53/0.70  # ...subsumed                          : 536
% 0.53/0.70  # ...remaining for further processing  : 452
% 0.53/0.70  # Other redundant clauses eliminated   : 129
% 0.53/0.70  # Clauses deleted for lack of memory   : 0
% 0.53/0.70  # Backward-subsumed                    : 79
% 0.53/0.70  # Backward-rewritten                   : 20
% 0.53/0.70  # Generated clauses                    : 13948
% 0.53/0.70  # ...of the previous two non-trivial   : 13160
% 0.53/0.70  # Contextual simplify-reflections      : 9
% 0.53/0.70  # Paramodulations                      : 13772
% 0.53/0.70  # Factorizations                       : 52
% 0.53/0.70  # Equation resolutions                 : 129
% 0.53/0.70  # Propositional unsat checks           : 0
% 0.53/0.70  #    Propositional check models        : 0
% 0.53/0.70  #    Propositional check unsatisfiable : 0
% 0.53/0.70  #    Propositional clauses             : 0
% 0.53/0.70  #    Propositional clauses after purity: 0
% 0.53/0.70  #    Propositional unsat core size     : 0
% 0.53/0.70  #    Propositional preprocessing time  : 0.000
% 0.53/0.70  #    Propositional encoding time       : 0.000
% 0.53/0.70  #    Propositional solver time         : 0.000
% 0.53/0.70  #    Success case prop preproc time    : 0.000
% 0.53/0.70  #    Success case prop encoding time   : 0.000
% 0.53/0.70  #    Success case prop solver time     : 0.000
% 0.53/0.70  # Current number of processed clauses  : 343
% 0.53/0.70  #    Positive orientable unit clauses  : 25
% 0.53/0.70  #    Positive unorientable unit clauses: 0
% 0.53/0.70  #    Negative unit clauses             : 5
% 0.53/0.70  #    Non-unit-clauses                  : 313
% 0.53/0.70  # Current number of unprocessed clauses: 11965
% 0.53/0.70  # ...number of literals in the above   : 76794
% 0.53/0.70  # Current number of archived formulas  : 0
% 0.53/0.70  # Current number of archived clauses   : 102
% 0.53/0.70  # Clause-clause subsumption calls (NU) : 13643
% 0.53/0.70  # Rec. Clause-clause subsumption calls : 4766
% 0.53/0.70  # Non-unit clause-clause subsumptions  : 554
% 0.53/0.70  # Unit Clause-clause subsumption calls : 429
% 0.53/0.70  # Rewrite failures with RHS unbound    : 0
% 0.53/0.70  # BW rewrite match attempts            : 59
% 0.53/0.70  # BW rewrite match successes           : 11
% 0.53/0.70  # Condensation attempts                : 0
% 0.53/0.70  # Condensation successes               : 0
% 0.53/0.70  # Termbank termtop insertions          : 280926
% 0.53/0.70  
% 0.53/0.70  # -------------------------------------------------
% 0.53/0.70  # User time                : 0.338 s
% 0.53/0.70  # System time              : 0.018 s
% 0.53/0.70  # Total time               : 0.356 s
% 0.53/0.70  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
