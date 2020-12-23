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
% DateTime   : Thu Dec  3 11:05:24 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 920 expanded)
%              Number of clauses        :   68 ( 384 expanded)
%              Number of leaves         :   19 ( 249 expanded)
%              Depth                    :   25
%              Number of atoms          :  337 (2387 expanded)
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

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_19,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X34,k1_zfmisc_1(X35))
        | r1_tarski(X34,X35) )
      & ( ~ r1_tarski(X34,X35)
        | m1_subset_1(X34,k1_zfmisc_1(X35)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_20,plain,(
    ! [X41,X42] :
      ( ( ~ v5_relat_1(X42,X41)
        | r1_tarski(k2_relat_1(X42),X41)
        | ~ v1_relat_1(X42) )
      & ( ~ r1_tarski(k2_relat_1(X42),X41)
        | v5_relat_1(X42,X41)
        | ~ v1_relat_1(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_22,plain,(
    ! [X36,X37,X38] :
      ( ~ r2_hidden(X36,X37)
      | ~ m1_subset_1(X37,k1_zfmisc_1(X38))
      | m1_subset_1(X36,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
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

fof(c_0_26,plain,(
    ! [X25] : k2_tarski(X25,X25) = k1_tarski(X25) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X26,X27] : k1_enumset1(X26,X26,X27) = k2_tarski(X26,X27) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X28,X29,X30] : k2_enumset1(X28,X28,X29,X30) = k1_enumset1(X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))
    & r2_hidden(esk5_0,esk3_0)
    & k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_36,plain,(
    ! [X49,X50,X51] :
      ( ( v4_relat_1(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) )
      & ( v5_relat_1(X51,X50)
        | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_38,plain,(
    ! [X39,X40] :
      ( ~ v1_relat_1(X39)
      | ~ m1_subset_1(X40,k1_zfmisc_1(X39))
      | v1_relat_1(X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_39,plain,(
    ! [X43,X44] : v1_relat_1(k2_zfmisc_1(X43,X44)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_40,plain,(
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

fof(c_0_41,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k1_relset_1(X52,X53,X54) = k1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_42,plain,(
    ! [X55,X56,X57] :
      ( ( ~ v1_funct_2(X57,X55,X56)
        | X55 = k1_relset_1(X55,X56,X57)
        | X56 = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X55 != k1_relset_1(X55,X56,X57)
        | v1_funct_2(X57,X55,X56)
        | X56 = k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ v1_funct_2(X57,X55,X56)
        | X55 = k1_relset_1(X55,X56,X57)
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X55 != k1_relset_1(X55,X56,X57)
        | v1_funct_2(X57,X55,X56)
        | X55 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( ~ v1_funct_2(X57,X55,X56)
        | X57 = k1_xboole_0
        | X55 = k1_xboole_0
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) )
      & ( X57 != k1_xboole_0
        | v1_funct_2(X57,X55,X56)
        | X55 = k1_xboole_0
        | X56 != k1_xboole_0
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_43,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X2)
    | ~ v5_relat_1(X3,X2)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k2_relat_1(X3)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_45,plain,
    ( esk2_2(X1,X2) = X1
    | X2 = k2_enumset1(X1,X1,X1,X1)
    | r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_46,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_48,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X4,X5,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_52,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_54,plain,(
    ! [X47,X48] :
      ( ~ r2_hidden(X47,X48)
      | ~ r1_tarski(X48,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_55,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_56,plain,
    ( X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_57,plain,
    ( k2_relat_1(X1) = k2_enumset1(X2,X2,X2,X2)
    | esk2_2(X2,k2_relat_1(X1)) = X2
    | m1_subset_1(esk2_2(X2,k2_relat_1(X1)),X3)
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_58,negated_conjecture,
    ( v5_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_49])])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X5,X2) ),
    inference(rw,[status(thm)],[c_0_50,c_0_35])).

cnf(c_0_61,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk6_0,esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(er,[status(thm)],[c_0_56])).

cnf(c_0_66,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk6_0)
    | esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59])])).

fof(c_0_67,plain,(
    ! [X45,X46] :
      ( ~ v1_relat_1(X46)
      | ~ v1_funct_1(X46)
      | ~ r2_hidden(X45,k1_relat_1(X46))
      | r2_hidden(k1_funct_1(X46,X45),k2_relat_1(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X3,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).

cnf(c_0_69,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k1_xboole_0
    | k1_relat_1(esk6_0) = esk3_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_47]),c_0_62])])).

cnf(c_0_70,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | X2 = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X2,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_72,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(esk6_0) = esk3_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70])).

fof(c_0_75,plain,(
    ! [X31] : ~ v1_xboole_0(k1_tarski(X31)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

fof(c_0_76,plain,(
    ! [X32,X33] :
      ( ~ m1_subset_1(X32,X33)
      | v1_xboole_0(X33)
      | r2_hidden(X32,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_77,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,X2) = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73]),c_0_59]),c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_79,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_76])).

cnf(c_0_81,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_82,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_83,plain,
    ( esk2_2(X1,k2_relat_1(X2)) = X1
    | r2_hidden(k1_funct_1(X2,X3),k2_enumset1(X1,X1,X1,X1))
    | r2_hidden(esk2_2(X1,k2_relat_1(X2)),k2_relat_1(X2))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_45])).

cnf(c_0_84,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))
    | r2_hidden(k1_funct_1(esk6_0,X2),k2_enumset1(X1,X1,X1,X1))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_74]),c_0_73]),c_0_59])])).

cnf(c_0_86,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk2_2(X1,X2),X2)
    | esk2_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_87,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = esk4_0
    | esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1 ),
    inference(spm,[status(thm)],[c_0_65,c_0_84])).

cnf(c_0_88,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) != esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_89,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_enumset1(X1,X1,X1,X1))
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_85,c_0_78])).

cnf(c_0_90,plain,
    ( X2 = k2_enumset1(X1,X1,X1,X1)
    | esk2_2(X1,X2) != X1
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_91,negated_conjecture,
    ( esk2_2(esk4_0,k2_relat_1(esk6_0)) = esk4_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_87])]),c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_89])).

cnf(c_0_93,negated_conjecture,
    ( k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0) = k2_relat_1(esk6_0)
    | ~ r2_hidden(esk4_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_94,negated_conjecture,
    ( esk2_2(X1,k2_relat_1(esk6_0)) = X1
    | k1_funct_1(esk6_0,esk5_0) = X1
    | esk4_0 = X1
    | r2_hidden(esk4_0,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_92,c_0_87])).

cnf(c_0_95,negated_conjecture,
    ( X1 = esk4_0
    | ~ r2_hidden(esk4_0,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( k2_enumset1(X1,X1,X1,X1) = k2_relat_1(esk6_0)
    | k1_funct_1(esk6_0,esk5_0) = X1
    | esk4_0 = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_94]),c_0_95])).

cnf(c_0_97,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | esk4_0 = X1
    | X2 = X1
    | ~ r2_hidden(X2,k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,k2_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_96])).

cnf(c_0_98,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | k1_funct_1(esk6_0,X2) = X1
    | esk4_0 = X1
    | ~ r2_hidden(X1,k2_relat_1(esk6_0))
    | ~ r2_hidden(X2,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_72]),c_0_73]),c_0_59]),c_0_74])])).

cnf(c_0_99,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = k1_funct_1(esk6_0,X1)
    | k1_funct_1(esk6_0,X2) = k1_funct_1(esk6_0,X1)
    | k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X2,esk3_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_72]),c_0_73]),c_0_59]),c_0_74])])).

cnf(c_0_100,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = k1_funct_1(esk6_0,X1)
    | k1_funct_1(esk6_0,X1) = esk4_0
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_78])).

cnf(c_0_101,negated_conjecture,
    ( k1_funct_1(esk6_0,X1) = esk4_0
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_100]),c_0_73]),c_0_59]),c_0_74])])).

cnf(c_0_102,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_78]),c_0_88])).

cnf(c_0_103,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk6_0,esk5_0),X1)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_102]),c_0_59])])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(X1)
    | r2_hidden(k1_funct_1(esk6_0,esk5_0),X1)
    | ~ v5_relat_1(esk6_0,X1) ),
    inference(spm,[status(thm)],[c_0_80,c_0_103])).

cnf(c_0_105,negated_conjecture,
    ( k1_funct_1(esk6_0,esk5_0) = X1
    | ~ v5_relat_1(esk6_0,k2_enumset1(X1,X1,X1,X1)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_104]),c_0_82])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_58]),c_0_88]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.63/0.84  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.63/0.84  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.63/0.84  #
% 0.63/0.84  # Preprocessing time       : 0.029 s
% 0.63/0.84  
% 0.63/0.84  # Proof found!
% 0.63/0.84  # SZS status Theorem
% 0.63/0.84  # SZS output start CNFRefutation
% 0.63/0.84  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.63/0.84  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 0.63/0.84  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 0.63/0.84  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.63/0.84  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.63/0.84  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.63/0.84  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.63/0.84  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.63/0.84  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.63/0.84  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.63/0.84  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.63/0.84  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.63/0.84  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.63/0.84  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.63/0.84  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.63/0.84  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.63/0.84  fof(t12_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X1),k2_relat_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 0.63/0.84  fof(fc2_xboole_0, axiom, ![X1]:~(v1_xboole_0(k1_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 0.63/0.84  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.63/0.84  fof(c_0_19, plain, ![X34, X35]:((~m1_subset_1(X34,k1_zfmisc_1(X35))|r1_tarski(X34,X35))&(~r1_tarski(X34,X35)|m1_subset_1(X34,k1_zfmisc_1(X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.63/0.84  fof(c_0_20, plain, ![X41, X42]:((~v5_relat_1(X42,X41)|r1_tarski(k2_relat_1(X42),X41)|~v1_relat_1(X42))&(~r1_tarski(k2_relat_1(X42),X41)|v5_relat_1(X42,X41)|~v1_relat_1(X42))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.63/0.84  fof(c_0_21, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.63/0.84  fof(c_0_22, plain, ![X36, X37, X38]:(~r2_hidden(X36,X37)|~m1_subset_1(X37,k1_zfmisc_1(X38))|m1_subset_1(X36,X38)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.63/0.84  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.63/0.84  cnf(c_0_24, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.63/0.84  fof(c_0_25, plain, ![X18, X19, X20, X21, X22, X23]:(((~r2_hidden(X20,X19)|X20=X18|X19!=k1_tarski(X18))&(X21!=X18|r2_hidden(X21,X19)|X19!=k1_tarski(X18)))&((~r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)!=X22|X23=k1_tarski(X22))&(r2_hidden(esk2_2(X22,X23),X23)|esk2_2(X22,X23)=X22|X23=k1_tarski(X22)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.63/0.84  fof(c_0_26, plain, ![X25]:k2_tarski(X25,X25)=k1_tarski(X25), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.63/0.84  fof(c_0_27, plain, ![X26, X27]:k1_enumset1(X26,X26,X27)=k2_tarski(X26,X27), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.63/0.84  fof(c_0_28, plain, ![X28, X29, X30]:k2_enumset1(X28,X28,X29,X30)=k1_enumset1(X28,X29,X30), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.63/0.84  fof(c_0_29, negated_conjecture, (((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0)))))&(r2_hidden(esk5_0,esk3_0)&k1_funct_1(esk6_0,esk5_0)!=esk4_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 0.63/0.84  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.63/0.84  cnf(c_0_31, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.63/0.84  cnf(c_0_32, plain, (r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.63/0.84  cnf(c_0_33, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.63/0.84  cnf(c_0_34, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.63/0.84  cnf(c_0_35, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.63/0.84  fof(c_0_36, plain, ![X49, X50, X51]:((v4_relat_1(X51,X49)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))&(v5_relat_1(X51,X50)|~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X49,X50))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.63/0.84  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k1_tarski(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.63/0.84  fof(c_0_38, plain, ![X39, X40]:(~v1_relat_1(X39)|(~m1_subset_1(X40,k1_zfmisc_1(X39))|v1_relat_1(X40))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.63/0.84  fof(c_0_39, plain, ![X43, X44]:v1_relat_1(k2_zfmisc_1(X43,X44)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.63/0.84  fof(c_0_40, plain, ![X7, X8, X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X11,X10)|(X11=X7|X11=X8|X11=X9)|X10!=k1_enumset1(X7,X8,X9))&(((X12!=X7|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))&(X12!=X8|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9)))&(X12!=X9|r2_hidden(X12,X10)|X10!=k1_enumset1(X7,X8,X9))))&((((esk1_4(X13,X14,X15,X16)!=X13|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15))&(esk1_4(X13,X14,X15,X16)!=X14|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(esk1_4(X13,X14,X15,X16)!=X15|~r2_hidden(esk1_4(X13,X14,X15,X16),X16)|X16=k1_enumset1(X13,X14,X15)))&(r2_hidden(esk1_4(X13,X14,X15,X16),X16)|(esk1_4(X13,X14,X15,X16)=X13|esk1_4(X13,X14,X15,X16)=X14|esk1_4(X13,X14,X15,X16)=X15)|X16=k1_enumset1(X13,X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.63/0.84  fof(c_0_41, plain, ![X52, X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k1_relset_1(X52,X53,X54)=k1_relat_1(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.63/0.84  fof(c_0_42, plain, ![X55, X56, X57]:((((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((~v1_funct_2(X57,X55,X56)|X57=k1_xboole_0|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X57!=k1_xboole_0|v1_funct_2(X57,X55,X56)|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.63/0.84  cnf(c_0_43, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.63/0.84  cnf(c_0_44, plain, (m1_subset_1(X1,X2)|~v5_relat_1(X3,X2)|~v1_relat_1(X3)|~r2_hidden(X1,k2_relat_1(X3))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.63/0.84  cnf(c_0_45, plain, (esk2_2(X1,X2)=X1|X2=k2_enumset1(X1,X1,X1,X1)|r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_33]), c_0_34]), c_0_35])).
% 0.63/0.84  cnf(c_0_46, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.63/0.84  cnf(c_0_47, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_33]), c_0_34]), c_0_35])).
% 0.63/0.84  cnf(c_0_48, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.63/0.84  cnf(c_0_49, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.63/0.84  cnf(c_0_50, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X4,X5,X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.63/0.84  cnf(c_0_51, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.63/0.84  cnf(c_0_52, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.63/0.84  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k1_tarski(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.63/0.84  fof(c_0_54, plain, ![X47, X48]:(~r2_hidden(X47,X48)|~r1_tarski(X48,X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.63/0.84  fof(c_0_55, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.63/0.84  cnf(c_0_56, plain, (X1=X3|X2!=k2_enumset1(X3,X3,X3,X3)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_33]), c_0_34]), c_0_35])).
% 0.63/0.84  cnf(c_0_57, plain, (k2_relat_1(X1)=k2_enumset1(X2,X2,X2,X2)|esk2_2(X2,k2_relat_1(X1))=X2|m1_subset_1(esk2_2(X2,k2_relat_1(X1)),X3)|~v5_relat_1(X1,X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.63/0.84  cnf(c_0_58, negated_conjecture, (v5_relat_1(esk6_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.63/0.84  cnf(c_0_59, negated_conjecture, (v1_relat_1(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_47]), c_0_49])])).
% 0.63/0.84  cnf(c_0_60, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X5,X2)), inference(rw,[status(thm)],[c_0_50, c_0_35])).
% 0.63/0.84  cnf(c_0_61, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.63/0.84  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk6_0,esk3_0,k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_33]), c_0_34]), c_0_35])).
% 0.63/0.84  cnf(c_0_63, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.63/0.84  cnf(c_0_64, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.63/0.84  cnf(c_0_65, plain, (X1=X2|~r2_hidden(X1,k2_enumset1(X2,X2,X2,X2))), inference(er,[status(thm)],[c_0_56])).
% 0.63/0.84  cnf(c_0_66, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk6_0)|esk2_2(X1,k2_relat_1(esk6_0))=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59])])).
% 0.63/0.84  fof(c_0_67, plain, ![X45, X46]:(~v1_relat_1(X46)|~v1_funct_1(X46)|(~r2_hidden(X45,k1_relat_1(X46))|r2_hidden(k1_funct_1(X46,X45),k2_relat_1(X46)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_1])])).
% 0.63/0.84  cnf(c_0_68, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X3,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_60])])).
% 0.63/0.84  cnf(c_0_69, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k1_xboole_0|k1_relat_1(esk6_0)=esk3_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_47]), c_0_62])])).
% 0.63/0.84  cnf(c_0_70, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.63/0.84  cnf(c_0_71, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|X2=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X2,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.63/0.84  cnf(c_0_72, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.63/0.84  cnf(c_0_73, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.63/0.84  cnf(c_0_74, negated_conjecture, (k1_relat_1(esk6_0)=esk3_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70])).
% 0.63/0.84  fof(c_0_75, plain, ![X31]:~v1_xboole_0(k1_tarski(X31)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).
% 0.63/0.84  fof(c_0_76, plain, ![X32, X33]:(~m1_subset_1(X32,X33)|(v1_xboole_0(X33)|r2_hidden(X32,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.63/0.84  cnf(c_0_77, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,X2)=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73]), c_0_59]), c_0_74])])).
% 0.63/0.84  cnf(c_0_78, negated_conjecture, (r2_hidden(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.63/0.84  cnf(c_0_79, plain, (~v1_xboole_0(k1_tarski(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.63/0.84  cnf(c_0_80, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_76])).
% 0.63/0.84  cnf(c_0_81, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|m1_subset_1(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(spm,[status(thm)],[c_0_77, c_0_78])).
% 0.63/0.84  cnf(c_0_82, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_33]), c_0_34]), c_0_35])).
% 0.63/0.84  cnf(c_0_83, plain, (esk2_2(X1,k2_relat_1(X2))=X1|r2_hidden(k1_funct_1(X2,X3),k2_enumset1(X1,X1,X1,X1))|r2_hidden(esk2_2(X1,k2_relat_1(X2)),k2_relat_1(X2))|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_72, c_0_45])).
% 0.63/0.84  cnf(c_0_84, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_82])).
% 0.63/0.84  cnf(c_0_85, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))|r2_hidden(k1_funct_1(esk6_0,X2),k2_enumset1(X1,X1,X1,X1))|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_74]), c_0_73]), c_0_59])])).
% 0.63/0.84  cnf(c_0_86, plain, (X2=k1_tarski(X1)|~r2_hidden(esk2_2(X1,X2),X2)|esk2_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.63/0.84  cnf(c_0_87, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=esk4_0|esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1), inference(spm,[status(thm)],[c_0_65, c_0_84])).
% 0.63/0.84  cnf(c_0_88, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)!=esk4_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.63/0.84  cnf(c_0_89, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_enumset1(X1,X1,X1,X1))|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_85, c_0_78])).
% 0.63/0.84  cnf(c_0_90, plain, (X2=k2_enumset1(X1,X1,X1,X1)|esk2_2(X1,X2)!=X1|~r2_hidden(esk2_2(X1,X2),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_33]), c_0_34]), c_0_35])).
% 0.63/0.84  cnf(c_0_91, negated_conjecture, (esk2_2(esk4_0,k2_relat_1(esk6_0))=esk4_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_87])]), c_0_88])).
% 0.63/0.84  cnf(c_0_92, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|r2_hidden(esk2_2(X1,k2_relat_1(esk6_0)),k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_89])).
% 0.63/0.84  cnf(c_0_93, negated_conjecture, (k2_enumset1(esk4_0,esk4_0,esk4_0,esk4_0)=k2_relat_1(esk6_0)|~r2_hidden(esk4_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.63/0.84  cnf(c_0_94, negated_conjecture, (esk2_2(X1,k2_relat_1(esk6_0))=X1|k1_funct_1(esk6_0,esk5_0)=X1|esk4_0=X1|r2_hidden(esk4_0,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_92, c_0_87])).
% 0.63/0.84  cnf(c_0_95, negated_conjecture, (X1=esk4_0|~r2_hidden(esk4_0,k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_93])).
% 0.63/0.84  cnf(c_0_96, negated_conjecture, (k2_enumset1(X1,X1,X1,X1)=k2_relat_1(esk6_0)|k1_funct_1(esk6_0,esk5_0)=X1|esk4_0=X1|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_94]), c_0_95])).
% 0.63/0.84  cnf(c_0_97, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|esk4_0=X1|X2=X1|~r2_hidden(X2,k2_relat_1(esk6_0))|~r2_hidden(X1,k2_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_65, c_0_96])).
% 0.63/0.84  cnf(c_0_98, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|k1_funct_1(esk6_0,X2)=X1|esk4_0=X1|~r2_hidden(X1,k2_relat_1(esk6_0))|~r2_hidden(X2,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_72]), c_0_73]), c_0_59]), c_0_74])])).
% 0.63/0.84  cnf(c_0_99, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=k1_funct_1(esk6_0,X1)|k1_funct_1(esk6_0,X2)=k1_funct_1(esk6_0,X1)|k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X2,esk3_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_72]), c_0_73]), c_0_59]), c_0_74])])).
% 0.63/0.84  cnf(c_0_100, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=k1_funct_1(esk6_0,X1)|k1_funct_1(esk6_0,X1)=esk4_0|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_99, c_0_78])).
% 0.63/0.84  cnf(c_0_101, negated_conjecture, (k1_funct_1(esk6_0,X1)=esk4_0|r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_100]), c_0_73]), c_0_59]), c_0_74])])).
% 0.63/0.84  cnf(c_0_102, negated_conjecture, (r2_hidden(k1_funct_1(esk6_0,esk5_0),k2_relat_1(esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_78]), c_0_88])).
% 0.63/0.84  cnf(c_0_103, negated_conjecture, (m1_subset_1(k1_funct_1(esk6_0,esk5_0),X1)|~v5_relat_1(esk6_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_102]), c_0_59])])).
% 0.63/0.84  cnf(c_0_104, negated_conjecture, (v1_xboole_0(X1)|r2_hidden(k1_funct_1(esk6_0,esk5_0),X1)|~v5_relat_1(esk6_0,X1)), inference(spm,[status(thm)],[c_0_80, c_0_103])).
% 0.63/0.84  cnf(c_0_105, negated_conjecture, (k1_funct_1(esk6_0,esk5_0)=X1|~v5_relat_1(esk6_0,k2_enumset1(X1,X1,X1,X1))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_104]), c_0_82])).
% 0.63/0.84  cnf(c_0_106, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_58]), c_0_88]), ['proof']).
% 0.63/0.84  # SZS output end CNFRefutation
% 0.63/0.84  # Proof object total steps             : 107
% 0.63/0.84  # Proof object clause steps            : 68
% 0.63/0.84  # Proof object formula steps           : 39
% 0.63/0.84  # Proof object conjectures             : 38
% 0.63/0.84  # Proof object clause conjectures      : 35
% 0.63/0.84  # Proof object formula conjectures     : 3
% 0.63/0.84  # Proof object initial clauses used    : 25
% 0.63/0.84  # Proof object initial formulas used   : 19
% 0.63/0.84  # Proof object generating inferences   : 34
% 0.63/0.84  # Proof object simplifying inferences  : 57
% 0.63/0.84  # Training examples: 0 positive, 0 negative
% 0.63/0.84  # Parsed axioms                        : 19
% 0.63/0.84  # Removed by relevancy pruning/SinE    : 0
% 0.63/0.84  # Initial clauses                      : 41
% 0.63/0.84  # Removed in clause preprocessing      : 3
% 0.63/0.84  # Initial clauses in saturation        : 38
% 0.63/0.84  # Processed clauses                    : 1339
% 0.63/0.84  # ...of these trivial                  : 23
% 0.63/0.84  # ...subsumed                          : 585
% 0.63/0.84  # ...remaining for further processing  : 731
% 0.63/0.84  # Other redundant clauses eliminated   : 113
% 0.63/0.84  # Clauses deleted for lack of memory   : 0
% 0.63/0.84  # Backward-subsumed                    : 135
% 0.63/0.84  # Backward-rewritten                   : 89
% 0.63/0.84  # Generated clauses                    : 23213
% 0.63/0.84  # ...of the previous two non-trivial   : 20754
% 0.63/0.84  # Contextual simplify-reflections      : 5
% 0.63/0.84  # Paramodulations                      : 23078
% 0.63/0.84  # Factorizations                       : 27
% 0.63/0.84  # Equation resolutions                 : 113
% 0.63/0.84  # Propositional unsat checks           : 0
% 0.63/0.84  #    Propositional check models        : 0
% 0.63/0.84  #    Propositional check unsatisfiable : 0
% 0.63/0.84  #    Propositional clauses             : 0
% 0.63/0.84  #    Propositional clauses after purity: 0
% 0.63/0.84  #    Propositional unsat core size     : 0
% 0.63/0.84  #    Propositional preprocessing time  : 0.000
% 0.63/0.84  #    Propositional encoding time       : 0.000
% 0.63/0.84  #    Propositional solver time         : 0.000
% 0.63/0.84  #    Success case prop preproc time    : 0.000
% 0.63/0.84  #    Success case prop encoding time   : 0.000
% 0.63/0.84  #    Success case prop solver time     : 0.000
% 0.63/0.84  # Current number of processed clauses  : 497
% 0.63/0.84  #    Positive orientable unit clauses  : 50
% 0.63/0.84  #    Positive unorientable unit clauses: 2
% 0.63/0.84  #    Negative unit clauses             : 5
% 0.63/0.84  #    Non-unit-clauses                  : 440
% 0.63/0.84  # Current number of unprocessed clauses: 18853
% 0.63/0.84  # ...number of literals in the above   : 118459
% 0.63/0.84  # Current number of archived formulas  : 0
% 0.63/0.84  # Current number of archived clauses   : 227
% 0.63/0.84  # Clause-clause subsumption calls (NU) : 27756
% 0.63/0.84  # Rec. Clause-clause subsumption calls : 6574
% 0.63/0.84  # Non-unit clause-clause subsumptions  : 588
% 0.63/0.84  # Unit Clause-clause subsumption calls : 1294
% 0.63/0.84  # Rewrite failures with RHS unbound    : 27
% 0.63/0.84  # BW rewrite match attempts            : 190
% 0.63/0.84  # BW rewrite match successes           : 34
% 0.63/0.84  # Condensation attempts                : 0
% 0.63/0.84  # Condensation successes               : 0
% 0.63/0.84  # Termbank termtop insertions          : 567250
% 0.63/0.85  
% 0.63/0.85  # -------------------------------------------------
% 0.63/0.85  # User time                : 0.493 s
% 0.63/0.85  # System time              : 0.015 s
% 0.63/0.85  # Total time               : 0.508 s
% 0.63/0.85  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
