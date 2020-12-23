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
% DateTime   : Thu Dec  3 11:05:11 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 893 expanded)
%              Number of clauses        :   67 ( 375 expanded)
%              Number of leaves         :   18 ( 240 expanded)
%              Depth                    :   25
%              Number of atoms          :  331 (2333 expanded)
%              Number of equality atoms :  136 (1090 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(t65_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,k1_tarski(X2))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
     => ( r2_hidden(X3,X1)
       => k1_funct_1(X4,X3) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_18,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_19,plain,(
    ! [X39,X40] :
      ( ( ~ v5_relat_1(X40,X39)
        | r1_tarski(k2_relat_1(X40),X39)
        | ~ v1_relat_1(X40) )
      & ( ~ r1_tarski(k2_relat_1(X40),X39)
        | v5_relat_1(X40,X39)
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_21,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_22,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X18,X19,X20,X21,X22,X23] :
      ( ( ~ r2_hidden(X20,X19)
        | X20 = X18
        | X19 != k1_tarski(X18) )
      & ( X21 != X18
        | r2_hidden(X21,X19)
        | X19 != k1_tarski(X18) )
      & ( ~ r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) != X22
        | X23 = k1_tarski(X22) )
      & ( r2_hidden(esk2_2(X22,X23),X23)
        | esk2_2(X22,X23) = X22
        | X23 = k1_tarski(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_25,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_28,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_31,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_35,plain,(
    ! [X48,X49,X50] :
      ( ( v4_relat_1(X50,X48)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( v5_relat_1(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | v1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_38,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X7
        | X11 = X8
        | X11 = X9
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X7
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k1_enumset1(X7,X8,X9) )
      & ( esk1_4(X13,X14,X15,X16) != X13
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X13,X14,X15,X16) != X14
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( esk1_4(X13,X14,X15,X16) != X15
        | ~ r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | X16 = k1_enumset1(X13,X14,X15) )
      & ( r2_hidden(esk1_4(X13,X14,X15,X16),X16)
        | esk1_4(X13,X14,X15,X16) = X13
        | esk1_4(X13,X14,X15,X16) = X14
        | esk1_4(X13,X14,X15,X16) = X15
        | X16 = k1_enumset1(X13,X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_39,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k1_relset_1(X51,X52,X53) = k1_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_40,plain,(
    ! [X54,X55,X56] :
      ( ( ~ v1_funct_2(X56,X54,X55)
        | X54 = k1_relset_1(X54,X55,X56)
        | X55 = k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_relset_1(X54,X55,X56)
        | v1_funct_2(X56,X54,X55)
        | X55 = k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( ~ v1_funct_2(X56,X54,X55)
        | X54 = k1_relset_1(X54,X55,X56)
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X54 != k1_relset_1(X54,X55,X56)
        | v1_funct_2(X56,X54,X55)
        | X54 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( ~ v1_funct_2(X56,X54,X55)
        | X56 = k1_xboole_0
        | X54 = k1_xboole_0
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X56 != k1_xboole_0
        | v1_funct_2(X56,X54,X55)
        | X54 = k1_xboole_0
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_41,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_43,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_44,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_49,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_51,plain,(
    ! [X43,X44] :
      ( ~ r2_hidden(X43,X44)
      | ~ r1_tarski(X44,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_52,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_54,plain,
    ( k2_relat_1(X1) = k2_enumset1(X2,X2,X2,X2)
    | esk2_2(X2,k2_relat_1(X1)) = X2
    | m1_subset_1(esk2_2(X2,k2_relat_1(X1)),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( v5_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_45])).

cnf(c_0_57,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_47,c_0_34])).

cnf(c_0_58,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_60,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk6_0)
    | esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])])).

fof(c_0_64,plain,(
    ! [X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ r2_hidden(X41,k1_relat_1(X42))
      | r2_hidden(k1_funct_1(X42,X41),k2_relat_1(X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).

cnf(c_0_66,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_45]),c_0_59])])).

cnf(c_0_67,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | X2 = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X2,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

fof(c_0_72,plain,(
    ! [X31] : ~ v1_xboole_0(k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_73,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_74,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,X2) = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_56]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_76,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_78,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_79,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_80,plain,
    ( esk2_2(X1,k2_relat_1(X2)) = X1
    | r2_hidden(k1_funct_1(X2,X3),k2_enumset1(X1,X1,X1,X1))
    | r2_hidden(esk2_2(X1,k2_relat_1(X2)),k2_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_43])).

cnf(c_0_81,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk6_0,X2),k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_71]),c_0_70]),c_0_56])])).

cnf(c_0_83,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_84,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = esk4_0
    | esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1 ),
    inference(spm,[status(thm)],[c_0_62,c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_86,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_enumset1(X1,X1,X1,X1))
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_75])).

cnf(c_0_87,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_88,negated_conjecture,
    ( esk2_2(esk4_0,k2_relat_1(esk6_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_84])]),c_0_85])).

cnf(c_0_89,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k2_relat_1(esk6_0)
    | ~ r2_hidden(esk4_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | esk4_0 = X1
    | r2_hidden(esk4_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_84])).

cnf(c_0_92,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(esk4_0,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk6_0)
    | k1_funct_1(esk6_0,esk5_0) = X1
    | esk4_0 = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_91]),c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | esk4_0 = X1
    | X2 = X1
    | ~ r2_hidden(X2,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_93])).

cnf(c_0_95,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | k1_funct_1(esk6_0,X2) = X1
    | esk4_0 = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_69]),c_0_70]),c_0_56]),c_0_71])])).

cnf(c_0_96,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = k1_funct_1(esk6_0,X1)
    | k1_funct_1(esk6_0,X2) = k1_funct_1(esk6_0,X1)
    | k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_69]),c_0_70]),c_0_56]),c_0_71])])).

cnf(c_0_97,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = k1_funct_1(esk6_0,X1)
    | k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_75])).

cnf(c_0_98,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_97]),c_0_70]),c_0_56]),c_0_71])])).

cnf(c_0_99,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_75]),c_0_85])).

cnf(c_0_100,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk6_0,esk5_0),X1)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_99]),c_0_56])])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(X1)
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),X1)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_100])).

cnf(c_0_102,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | ~ v5_relat_1(esk6_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_101]),c_0_79])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_55]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.92/1.11  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.92/1.11  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.92/1.11  #
% 0.92/1.11  # Preprocessing time       : 0.019 s
% 0.92/1.11  
% 0.92/1.11  # Proof found!
% 0.92/1.11  # SZS status Theorem
% 0.92/1.11  # SZS output start CNFRefutation
% 0.92/1.11  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.92/1.11  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.92/1.11  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.92/1.11  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.92/1.11  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.92/1.11  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.92/1.11  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.92/1.11  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.92/1.11  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.92/1.11  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.92/1.11  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.92/1.11  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.92/1.11  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.92/1.11  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.92/1.11  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.92/1.11  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.92/1.11  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.92/1.11  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.92/1.11  fof(c_0_18, plain, ![X34, X35]:((~m1_subset_1(X34,k1_zfmisc_1(X35))|r1_tarski(X34,X35))&(~r1_tarski(X34,X35)|m1_subset_1(X34,k1_zfmisc_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.92/1.11  fof(c_0_19, plain, ![X39, X40]:((~v5_relat_1(X40,X39)|r1_tarski(k2_relat_1(X40),X39)|~v1_relat_1(X40))&(~r1_tarski(k2_relat_1(X40),X39)|v5_relat_1(X40,X39)|~v1_relat_1(X40))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.92/1.11  fof(c_0_20, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.92/1.11  fof(c_0_21, plain, ![X36, X37, X38]:(~r2_hidden(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(X38))|m1_subset_1(X36,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.92/1.11  cnf(c_0_22, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.92/1.11  cnf(c_0_23, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.92/1.11  fof(c_0_24, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|X20=X18|X19!=k1_tarski(X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_tarski(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)!=X22|X23=k1_tarski(X22))&(r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)=X22|X23=k1_tarski(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.92/1.11  fof(c_0_25, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.92/1.11  fof(c_0_26, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.92/1.11  fof(c_0_27, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.92/1.11  fof(c_0_28, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_20])])])).
% 0.92/1.11  cnf(c_0_29, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.92/1.11  cnf(c_0_30, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.92/1.11  cnf(c_0_31, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.11  cnf(c_0_32, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.92/1.11  cnf(c_0_33, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.92/1.11  cnf(c_0_34, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.92/1.11  fof(c_0_35, plain, ![X48, X49, X50]:((v4_relat_1(X50,X48)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))&(v5_relat_1(X50,X49)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.92/1.11  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.11  fof(c_0_37, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|v1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.92/1.11  fof(c_0_38, plain, ![X7, X8, X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X11,X10)|(X11=X7|X11=X8|X11=X9)|X10!=k1_enumset1(X7,X8,X9))&(((X12!=X7|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))&(X12!=X8|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9)))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))))&((((esk1_4(X13,X14,X15,X16)!=X13|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15))&(esk1_4(X13,X14,X15,X16)!=X14|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(esk1_4(X13,X14,X15,X16)!=X15|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(r2_hidden(esk1_4(X13,X14,X15,X16),X16)|(esk1_4(X13,X14,X15,X16)=X13|esk1_4(X13,X14,X15,X16)=X14|esk1_4(X13,X14,X15,X16)=X15)|X16=k1_enumset1(X13,X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.92/1.11  fof(c_0_39, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k1_relset_1(X51,X52,X53)=k1_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.92/1.11  fof(c_0_40, plain, ![X54, X55, X56]:((((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&((~v1_funct_2(X56,X54,X55)|X56=k1_xboole_0|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X56!=k1_xboole_0|v1_funct_2(X56,X54,X55)|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.92/1.11  cnf(c_0_41, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.11  cnf(c_0_42, plain, (m1_subset_1(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.92/1.11  cnf(c_0_43, plain, (esk2_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.11  cnf(c_0_44, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.92/1.11  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.11  cnf(c_0_46, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.92/1.11  cnf(c_0_47, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.92/1.11  cnf(c_0_48, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.92/1.11  cnf(c_0_49, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.92/1.11  cnf(c_0_50, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.11  fof(c_0_51, plain, ![X43, X44]:(~r2_hidden(X43,X44)|~r1_tarski(X44,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.92/1.11  fof(c_0_52, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.92/1.11  cnf(c_0_53, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.11  cnf(c_0_54, plain, (k2_relat_1(X1)=k2_enumset1(X2,X2,X2,X2)|esk2_2(X2,k2_relat_1(X1))=X2|m1_subset_1(esk2_2(X2,k2_relat_1(X1)),X3)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.92/1.11  cnf(c_0_55, negated_conjecture, (v5_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.92/1.11  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk6_0)), inference(spm,[status(thm)],[c_0_46, c_0_45])).
% 0.92/1.11  cnf(c_0_57, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_47, c_0_34])).
% 0.92/1.11  cnf(c_0_58, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.92/1.11  cnf(c_0_59, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.11  cnf(c_0_60, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.92/1.11  cnf(c_0_61, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.92/1.11  cnf(c_0_62, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_53])).
% 0.92/1.11  cnf(c_0_63, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk6_0)|esk2_2(X1,k2_relat_1(esk6_0))=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])])).
% 0.92/1.11  fof(c_0_64, plain, ![X41, X42]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~r2_hidden(X41,k1_relat_1(X42))|r2_hidden(k1_funct_1(X42,X41),k2_relat_1(X42)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.92/1.11  cnf(c_0_65, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_57])])).
% 0.92/1.11  cnf(c_0_66, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_45]), c_0_59])])).
% 0.92/1.11  cnf(c_0_67, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.92/1.11  cnf(c_0_68, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|X2=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X2,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.92/1.11  cnf(c_0_69, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.92/1.11  cnf(c_0_70, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.11  cnf(c_0_71, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])).
% 0.92/1.11  fof(c_0_72, plain, ![X31]:~v1_xboole_0(k1_tarski(X31)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.92/1.11  fof(c_0_73, plain, ![X32, X33]:(~m1_subset_1(X32,X33)|(v1_xboole_0(X33)|r2_hidden(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.92/1.11  cnf(c_0_74, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,X2)=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_56]), c_0_71])])).
% 0.92/1.11  cnf(c_0_75, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.11  cnf(c_0_76, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.92/1.11  cnf(c_0_77, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.92/1.11  cnf(c_0_78, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.92/1.11  cnf(c_0_79, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.11  cnf(c_0_80, plain, (esk2_2(X1,k2_relat_1(X2))=X1|r2_hidden(k1_funct_1(X2,X3),k2_enumset1(X1,X1,X1,X1))|r2_hidden(esk2_2(X1,k2_relat_1(X2)),k2_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_69, c_0_43])).
% 0.92/1.11  cnf(c_0_81, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])).
% 0.92/1.11  cnf(c_0_82, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))|r2_hidden(k1_funct_1(esk6_0,X2),k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_71]), c_0_70]), c_0_56])])).
% 0.92/1.11  cnf(c_0_83, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.92/1.11  cnf(c_0_84, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=esk4_0|esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1), inference(spm,[status(thm)],[c_0_62, c_0_81])).
% 0.92/1.11  cnf(c_0_85, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.92/1.11  cnf(c_0_86, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_enumset1(X1,X1,X1,X1))|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_82, c_0_75])).
% 0.92/1.11  cnf(c_0_87, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_83, c_0_32]), c_0_33]), c_0_34])).
% 0.92/1.11  cnf(c_0_88, negated_conjecture, (esk2_2(esk4_0,k2_relat_1(esk6_0))=esk4_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_84])]), c_0_85])).
% 0.92/1.11  cnf(c_0_89, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_86])).
% 0.92/1.11  cnf(c_0_90, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k2_relat_1(esk6_0)|~r2_hidden(esk4_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.92/1.11  cnf(c_0_91, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|esk4_0=X1|r2_hidden(esk4_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_89, c_0_84])).
% 0.92/1.11  cnf(c_0_92, negated_conjecture, (X1=esk4_0|~r2_hidden(esk4_0,k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_90])).
% 0.92/1.11  cnf(c_0_93, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk6_0)|k1_funct_1(esk6_0,esk5_0)=X1|esk4_0=X1|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_91]), c_0_92])).
% 0.92/1.11  cnf(c_0_94, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|esk4_0=X1|X2=X1|~r2_hidden(X2,k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_62, c_0_93])).
% 0.92/1.11  cnf(c_0_95, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|k1_funct_1(esk6_0,X2)=X1|esk4_0=X1|~r2_hidden(X1,k2_relat_1(esk6_0))|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_69]), c_0_70]), c_0_56]), c_0_71])])).
% 0.92/1.11  cnf(c_0_96, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=k1_funct_1(esk6_0,X1)|k1_funct_1(esk6_0,X2)=k1_funct_1(esk6_0,X1)|k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95, c_0_69]), c_0_70]), c_0_56]), c_0_71])])).
% 0.92/1.11  cnf(c_0_97, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=k1_funct_1(esk6_0,X1)|k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_96, c_0_75])).
% 0.92/1.11  cnf(c_0_98, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_97]), c_0_70]), c_0_56]), c_0_71])])).
% 0.92/1.11  cnf(c_0_99, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_75]), c_0_85])).
% 0.92/1.11  cnf(c_0_100, negated_conjecture, (m1_subset_1(k1_funct_1(esk6_0,esk5_0),X1)|~v5_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_99]), c_0_56])])).
% 0.92/1.11  cnf(c_0_101, negated_conjecture, (v1_xboole_0(X1)|r2_hidden(k1_funct_1(esk6_0,esk5_0),X1)|~v5_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_77, c_0_100])).
% 0.92/1.11  cnf(c_0_102, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|~v5_relat_1(esk6_0,k2_enumset1(X1,X1,X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_101]), c_0_79])).
% 0.92/1.11  cnf(c_0_103, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_102, c_0_55]), c_0_85]), ['proof']).
% 0.92/1.11  # SZS output end CNFRefutation
% 0.92/1.11  # Proof object total steps             : 104
% 0.92/1.11  # Proof object clause steps            : 67
% 0.92/1.11  # Proof object formula steps           : 37
% 0.92/1.11  # Proof object conjectures             : 38
% 0.92/1.11  # Proof object clause conjectures      : 35
% 0.92/1.11  # Proof object formula conjectures     : 3
% 0.92/1.11  # Proof object initial clauses used    : 24
% 0.92/1.11  # Proof object initial formulas used   : 18
% 0.92/1.11  # Proof object generating inferences   : 34
% 0.92/1.11  # Proof object simplifying inferences  : 55
% 0.92/1.11  # Training examples: 0 positive, 0 negative
% 0.92/1.11  # Parsed axioms                        : 18
% 0.92/1.11  # Removed by relevancy pruning/SinE    : 0
% 0.92/1.11  # Initial clauses                      : 40
% 0.92/1.11  # Removed in clause preprocessing      : 3
% 0.92/1.11  # Initial clauses in saturation        : 37
% 0.92/1.11  # Processed clauses                    : 1463
% 0.92/1.11  # ...of these trivial                  : 26
% 0.92/1.11  # ...subsumed                          : 598
% 0.92/1.11  # ...remaining for further processing  : 839
% 0.92/1.11  # Other redundant clauses eliminated   : 119
% 0.92/1.11  # Clauses deleted for lack of memory   : 0
% 0.92/1.11  # Backward-subsumed                    : 130
% 0.92/1.11  # Backward-rewritten                   : 113
% 0.92/1.11  # Generated clauses                    : 41367
% 0.92/1.11  # ...of the previous two non-trivial   : 37323
% 0.92/1.11  # Contextual simplify-reflections      : 5
% 0.92/1.11  # Paramodulations                      : 41222
% 0.92/1.11  # Factorizations                       : 31
% 0.92/1.11  # Equation resolutions                 : 119
% 0.92/1.11  # Propositional unsat checks           : 0
% 0.92/1.11  #    Propositional check models        : 0
% 0.92/1.11  #    Propositional check unsatisfiable : 0
% 0.92/1.11  #    Propositional clauses             : 0
% 0.92/1.11  #    Propositional clauses after purity: 0
% 0.92/1.11  #    Propositional unsat core size     : 0
% 0.92/1.11  #    Propositional preprocessing time  : 0.000
% 0.92/1.11  #    Propositional encoding time       : 0.000
% 0.92/1.11  #    Propositional solver time         : 0.000
% 0.92/1.11  #    Success case prop preproc time    : 0.000
% 0.92/1.11  #    Success case prop encoding time   : 0.000
% 0.92/1.11  #    Success case prop solver time     : 0.000
% 0.92/1.11  # Current number of processed clauses  : 586
% 0.92/1.11  #    Positive orientable unit clauses  : 101
% 0.92/1.11  #    Positive unorientable unit clauses: 2
% 0.92/1.11  #    Negative unit clauses             : 5
% 0.92/1.11  #    Non-unit-clauses                  : 478
% 0.92/1.11  # Current number of unprocessed clauses: 35247
% 0.92/1.11  # ...number of literals in the above   : 206367
% 0.92/1.11  # Current number of archived formulas  : 0
% 0.92/1.11  # Current number of archived clauses   : 246
% 0.92/1.11  # Clause-clause subsumption calls (NU) : 41237
% 0.92/1.11  # Rec. Clause-clause subsumption calls : 10117
% 0.92/1.11  # Non-unit clause-clause subsumptions  : 581
% 0.92/1.11  # Unit Clause-clause subsumption calls : 2200
% 0.92/1.11  # Rewrite failures with RHS unbound    : 27
% 0.92/1.11  # BW rewrite match attempts            : 881
% 0.92/1.11  # BW rewrite match successes           : 27
% 0.92/1.11  # Condensation attempts                : 0
% 0.92/1.11  # Condensation successes               : 0
% 0.92/1.11  # Termbank termtop insertions          : 1090222
% 0.92/1.11  
% 0.92/1.11  # -------------------------------------------------
% 0.92/1.11  # User time                : 0.749 s
% 0.92/1.11  # System time              : 0.022 s
% 0.92/1.11  # Total time               : 0.771 s
% 0.92/1.11  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
