%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:04 EST 2020

% Result     : Theorem 0.16s
% Output     : CNFRefutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 679 expanded)
%              Number of clauses        :   65 ( 259 expanded)
%              Number of leaves         :   29 ( 203 expanded)
%              Depth                    :   12
%              Number of atoms          :  265 (1110 expanded)
%              Number of equality atoms :   91 ( 567 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t64_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,k1_tarski(X1),X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

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

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t65_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(X1,k1_tarski(X2)) = X1
    <=> ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t92_xboole_1,axiom,(
    ! [X1] : k5_xboole_0(X1,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(t209_relat_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X2,X1) )
     => X2 = k7_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(t21_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_30,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,k1_tarski(esk1_0),esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))
    & esk2_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).

fof(c_0_31,plain,(
    ! [X16] : k2_tarski(X16,X16) = k1_tarski(X16) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_32,plain,(
    ! [X17,X18] : k1_enumset1(X17,X17,X18) = k2_tarski(X17,X18) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_33,plain,(
    ! [X19,X20,X21] : k2_enumset1(X19,X19,X20,X21) = k1_enumset1(X19,X20,X21) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_34,plain,(
    ! [X22,X23,X24,X25] : k3_enumset1(X22,X22,X23,X24,X25) = k2_enumset1(X22,X23,X24,X25) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_35,plain,(
    ! [X26,X27,X28,X29,X30] : k4_enumset1(X26,X26,X27,X28,X29,X30) = k3_enumset1(X26,X27,X28,X29,X30) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_36,plain,(
    ! [X31,X32,X33,X34,X35,X36] : k5_enumset1(X31,X31,X32,X33,X34,X35,X36) = k4_enumset1(X31,X32,X33,X34,X35,X36) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_37,plain,(
    ! [X37,X38,X39,X40,X41,X42,X43] : k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43) = k5_enumset1(X37,X38,X39,X40,X41,X42,X43) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_38,plain,(
    ! [X67,X68] :
      ( ~ v1_relat_1(X68)
      | ~ v1_funct_1(X68)
      | k1_relat_1(X68) != k1_tarski(X67)
      | k2_relat_1(X68) = k1_tarski(k1_funct_1(X68,X67)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_39,plain,(
    ! [X52,X53] :
      ( ~ v1_relat_1(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X52))
      | v1_relat_1(X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_48,plain,(
    ! [X56,X57] : v1_relat_1(k2_zfmisc_1(X56,X57)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_49,plain,(
    ! [X69,X70,X71] :
      ( ( v4_relat_1(X71,X69)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) )
      & ( v5_relat_1(X71,X70)
        | ~ m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_52,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_54,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_55,plain,(
    ! [X72,X73,X74,X75] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))
      | k7_relset_1(X72,X73,X74,X75) = k9_relat_1(X74,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_56,plain,(
    ! [X50,X51] :
      ( ( ~ m1_subset_1(X50,k1_zfmisc_1(X51))
        | r1_tarski(X50,X51) )
      & ( ~ r1_tarski(X50,X51)
        | m1_subset_1(X50,k1_zfmisc_1(X51)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_57,plain,(
    ! [X54,X55] :
      ( ( ~ v4_relat_1(X55,X54)
        | r1_tarski(k1_relat_1(X55),X54)
        | ~ v1_relat_1(X55) )
      & ( ~ r1_tarski(k1_relat_1(X55),X54)
        | v4_relat_1(X55,X54)
        | ~ v1_relat_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_58,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_60,plain,
    ( k2_relat_1(X1) = k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_41]),c_0_41]),c_0_42]),c_0_42]),c_0_43]),c_0_43]),c_0_44]),c_0_44]),c_0_45]),c_0_45]),c_0_46]),c_0_46]),c_0_47]),c_0_47])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_62,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54])])).

cnf(c_0_63,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_64,plain,(
    ! [X63,X64] :
      ( ( r1_tarski(k1_relat_1(X63),k1_relat_1(X64))
        | ~ r1_tarski(X63,X64)
        | ~ v1_relat_1(X64)
        | ~ v1_relat_1(X63) )
      & ( r1_tarski(k2_relat_1(X63),k2_relat_1(X64))
        | ~ r1_tarski(X63,X64)
        | ~ v1_relat_1(X64)
        | ~ v1_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_65,plain,(
    ! [X58,X59] :
      ( ~ v1_relat_1(X59)
      | k2_relat_1(k7_relat_1(X59,X58)) = k9_relat_1(X59,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

cnf(c_0_66,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_67,plain,(
    ! [X8,X9] :
      ( ( r1_tarski(X8,X9)
        | X8 != X9 )
      & ( r1_tarski(X9,X8)
        | X8 != X9 )
      & ( ~ r1_tarski(X8,X9)
        | ~ r1_tarski(X9,X8)
        | X8 = X9 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( v4_relat_1(esk4_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_53])).

fof(c_0_70,plain,(
    ! [X44,X45] :
      ( ( ~ r1_tarski(k1_tarski(X44),X45)
        | r2_hidden(X44,X45) )
      & ( ~ r2_hidden(X44,X45)
        | r1_tarski(k1_tarski(X44),X45) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_71,plain,(
    ! [X48,X49] :
      ( ( k4_xboole_0(X48,k1_tarski(X49)) != X48
        | ~ r2_hidden(X49,X48) )
      & ( r2_hidden(X49,X48)
        | k4_xboole_0(X48,k1_tarski(X49)) = X48 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).

fof(c_0_72,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k5_xboole_0(X10,k3_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_73,plain,(
    ! [X46,X47] :
      ( ( k2_zfmisc_1(X46,X47) != k1_xboole_0
        | X46 = k1_xboole_0
        | X47 = k1_xboole_0 )
      & ( X46 != k1_xboole_0
        | k2_zfmisc_1(X46,X47) = k1_xboole_0 )
      & ( X47 != k1_xboole_0
        | k2_zfmisc_1(X46,X47) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_74,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_relat_1(esk4_0)
    | ~ r1_tarski(k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,esk3_0),k2_relat_1(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_62])])).

cnf(c_0_75,negated_conjecture,
    ( k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,X1) = k9_relat_1(esk4_0,X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_53])).

cnf(c_0_76,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_77,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_78,plain,
    ( v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_66])).

cnf(c_0_79,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_62])])).

cnf(c_0_81,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_82,plain,
    ( r2_hidden(X1,X2)
    | k4_xboole_0(X2,k1_tarski(X1)) = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_83,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

fof(c_0_84,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(X12,X13)
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_85,plain,(
    ! [X15] : k5_xboole_0(X15,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t92_xboole_1])).

cnf(c_0_86,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_87,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_relat_1(esk4_0)
    | ~ r1_tarski(k9_relat_1(esk4_0,esk3_0),k2_relat_1(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_88,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X3))
    | ~ v1_relat_1(X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k7_relat_1(X1,X2),X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])).

cnf(c_0_89,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_relat_1(esk4_0)
    | ~ r1_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_90,plain,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_91,plain,
    ( k5_xboole_0(X2,k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X2
    | r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_41]),c_0_42]),c_0_83]),c_0_43]),c_0_44]),c_0_45]),c_0_46]),c_0_47])).

cnf(c_0_92,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_93,plain,
    ( k5_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

fof(c_0_94,plain,(
    ! [X60,X61] :
      ( ~ v1_relat_1(X61)
      | ~ v4_relat_1(X61,X60)
      | X61 = k7_relat_1(X61,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).

cnf(c_0_95,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_86])).

cnf(c_0_96,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_97,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) != k1_relat_1(esk4_0)
    | ~ r1_tarski(k7_relat_1(esk4_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_62])])).

cnf(c_0_98,negated_conjecture,
    ( k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0) = k1_relat_1(esk4_0)
    | ~ r2_hidden(esk1_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_99,plain,
    ( k1_xboole_0 = X1
    | r2_hidden(X2,X1)
    | ~ r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_93])).

cnf(c_0_100,plain,
    ( X1 = k7_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v4_relat_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_101,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_102,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_95])).

fof(c_0_103,plain,(
    ! [X14] : r1_tarski(k1_xboole_0,X14) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_104,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(esk1_0,k1_relat_1(esk4_0))
    | ~ r1_tarski(k7_relat_1(esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_106,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | r2_hidden(esk1_0,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_99,c_0_80])).

fof(c_0_107,plain,(
    ! [X65,X66] :
      ( ~ v1_relat_1(X66)
      | r1_tarski(k7_relat_1(X66,X65),X66) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_108,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))) ),
    inference(rw,[status(thm)],[c_0_59,c_0_75])).

cnf(c_0_109,plain,
    ( k9_relat_1(X1,X2) = k2_relat_1(X1)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_77,c_0_100])).

cnf(c_0_110,plain,
    ( r1_tarski(k2_relat_1(X1),k1_xboole_0)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_101]),c_0_102])])).

cnf(c_0_111,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_103])).

cnf(c_0_112,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_104])).

fof(c_0_113,plain,(
    ! [X62] :
      ( ~ v1_relat_1(X62)
      | r1_tarski(X62,k2_zfmisc_1(k1_relat_1(X62),k2_relat_1(X62))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).

cnf(c_0_114,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0
    | ~ r1_tarski(k7_relat_1(esk4_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_115,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_116,negated_conjecture,
    ( ~ v4_relat_1(esk4_0,esk3_0)
    | ~ r1_tarski(k2_relat_1(esk4_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_62])])).

cnf(c_0_117,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_110]),c_0_111])])).

cnf(c_0_118,plain,
    ( v4_relat_1(X1,X2)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_112,c_0_66])).

cnf(c_0_119,plain,
    ( r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_113])).

cnf(c_0_120,negated_conjecture,
    ( k1_relat_1(esk4_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_115]),c_0_62])])).

cnf(c_0_121,negated_conjecture,
    ( ~ r1_tarski(esk4_0,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_117]),c_0_111]),c_0_62])]),c_0_118])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_95]),c_0_62])]),c_0_121]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:29:45 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  # Version: 2.5pre002
% 0.12/0.31  # No SInE strategy applied
% 0.12/0.31  # Trying AutoSched0 for 299 seconds
% 0.16/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.16/0.37  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.16/0.37  #
% 0.16/0.37  # Preprocessing time       : 0.028 s
% 0.16/0.37  # Presaturation interreduction done
% 0.16/0.37  
% 0.16/0.37  # Proof found!
% 0.16/0.37  # SZS status Theorem
% 0.16/0.37  # SZS output start CNFRefutation
% 0.16/0.37  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.16/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.16/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.16/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.16/0.37  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.16/0.37  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.16/0.37  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.16/0.37  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.16/0.37  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.16/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.16/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.16/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.16/0.37  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.16/0.37  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.16/0.37  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.16/0.37  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.16/0.37  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 0.16/0.37  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.16/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.16/0.37  fof(t65_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(X1,k1_tarski(X2))=X1<=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 0.16/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.16/0.37  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.16/0.37  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 0.16/0.37  fof(t92_xboole_1, axiom, ![X1]:k5_xboole_0(X1,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 0.16/0.37  fof(t209_relat_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v4_relat_1(X2,X1))=>X2=k7_relat_1(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 0.16/0.37  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.16/0.37  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.16/0.37  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.16/0.37  fof(t21_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 0.16/0.37  fof(c_0_29, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.16/0.37  fof(c_0_30, negated_conjecture, (((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,k1_tarski(esk1_0),esk2_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0))))&(esk2_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_29])])])).
% 0.16/0.37  fof(c_0_31, plain, ![X16]:k2_tarski(X16,X16)=k1_tarski(X16), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.16/0.37  fof(c_0_32, plain, ![X17, X18]:k1_enumset1(X17,X17,X18)=k2_tarski(X17,X18), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.16/0.37  fof(c_0_33, plain, ![X19, X20, X21]:k2_enumset1(X19,X19,X20,X21)=k1_enumset1(X19,X20,X21), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.16/0.37  fof(c_0_34, plain, ![X22, X23, X24, X25]:k3_enumset1(X22,X22,X23,X24,X25)=k2_enumset1(X22,X23,X24,X25), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.16/0.37  fof(c_0_35, plain, ![X26, X27, X28, X29, X30]:k4_enumset1(X26,X26,X27,X28,X29,X30)=k3_enumset1(X26,X27,X28,X29,X30), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.16/0.37  fof(c_0_36, plain, ![X31, X32, X33, X34, X35, X36]:k5_enumset1(X31,X31,X32,X33,X34,X35,X36)=k4_enumset1(X31,X32,X33,X34,X35,X36), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.16/0.37  fof(c_0_37, plain, ![X37, X38, X39, X40, X41, X42, X43]:k6_enumset1(X37,X37,X38,X39,X40,X41,X42,X43)=k5_enumset1(X37,X38,X39,X40,X41,X42,X43), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.16/0.37  fof(c_0_38, plain, ![X67, X68]:(~v1_relat_1(X68)|~v1_funct_1(X68)|(k1_relat_1(X68)!=k1_tarski(X67)|k2_relat_1(X68)=k1_tarski(k1_funct_1(X68,X67)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.16/0.37  fof(c_0_39, plain, ![X52, X53]:(~v1_relat_1(X52)|(~m1_subset_1(X53,k1_zfmisc_1(X52))|v1_relat_1(X53))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.16/0.37  cnf(c_0_40, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk1_0),esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.37  cnf(c_0_41, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.16/0.37  cnf(c_0_42, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.16/0.37  cnf(c_0_43, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.16/0.37  cnf(c_0_44, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.16/0.37  cnf(c_0_45, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.16/0.37  cnf(c_0_46, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.16/0.37  cnf(c_0_47, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.16/0.37  fof(c_0_48, plain, ![X56, X57]:v1_relat_1(k2_zfmisc_1(X56,X57)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.16/0.37  fof(c_0_49, plain, ![X69, X70, X71]:((v4_relat_1(X71,X69)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))&(v5_relat_1(X71,X70)|~m1_subset_1(X71,k1_zfmisc_1(k2_zfmisc_1(X69,X70))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.16/0.37  cnf(c_0_50, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk1_0),esk2_0,esk4_0,esk3_0),k1_tarski(k1_funct_1(esk4_0,esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.37  cnf(c_0_51, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.16/0.37  cnf(c_0_52, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.16/0.37  cnf(c_0_53, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.16/0.37  cnf(c_0_54, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.16/0.37  fof(c_0_55, plain, ![X72, X73, X74, X75]:(~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X72,X73)))|k7_relset_1(X72,X73,X74,X75)=k9_relat_1(X74,X75)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.16/0.37  fof(c_0_56, plain, ![X50, X51]:((~m1_subset_1(X50,k1_zfmisc_1(X51))|r1_tarski(X50,X51))&(~r1_tarski(X50,X51)|m1_subset_1(X50,k1_zfmisc_1(X51)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.16/0.37  fof(c_0_57, plain, ![X54, X55]:((~v4_relat_1(X55,X54)|r1_tarski(k1_relat_1(X55),X54)|~v1_relat_1(X55))&(~r1_tarski(k1_relat_1(X55),X54)|v4_relat_1(X55,X54)|~v1_relat_1(X55))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.16/0.37  cnf(c_0_58, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.16/0.37  cnf(c_0_59, negated_conjecture, (~r1_tarski(k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.16/0.37  cnf(c_0_60, plain, (k2_relat_1(X1)=k6_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_41]), c_0_41]), c_0_42]), c_0_42]), c_0_43]), c_0_43]), c_0_44]), c_0_44]), c_0_45]), c_0_45]), c_0_46]), c_0_46]), c_0_47]), c_0_47])).
% 0.16/0.37  cnf(c_0_61, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.16/0.37  cnf(c_0_62, negated_conjecture, (v1_relat_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54])])).
% 0.16/0.37  cnf(c_0_63, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.16/0.37  fof(c_0_64, plain, ![X63, X64]:((r1_tarski(k1_relat_1(X63),k1_relat_1(X64))|~r1_tarski(X63,X64)|~v1_relat_1(X64)|~v1_relat_1(X63))&(r1_tarski(k2_relat_1(X63),k2_relat_1(X64))|~r1_tarski(X63,X64)|~v1_relat_1(X64)|~v1_relat_1(X63))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.16/0.37  fof(c_0_65, plain, ![X58, X59]:(~v1_relat_1(X59)|k2_relat_1(k7_relat_1(X59,X58))=k9_relat_1(X59,X58)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.16/0.37  cnf(c_0_66, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.16/0.37  fof(c_0_67, plain, ![X8, X9]:(((r1_tarski(X8,X9)|X8!=X9)&(r1_tarski(X9,X8)|X8!=X9))&(~r1_tarski(X8,X9)|~r1_tarski(X9,X8)|X8=X9)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.16/0.37  cnf(c_0_68, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.16/0.37  cnf(c_0_69, negated_conjecture, (v4_relat_1(esk4_0,k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))), inference(spm,[status(thm)],[c_0_58, c_0_53])).
% 0.16/0.37  fof(c_0_70, plain, ![X44, X45]:((~r1_tarski(k1_tarski(X44),X45)|r2_hidden(X44,X45))&(~r2_hidden(X44,X45)|r1_tarski(k1_tarski(X44),X45))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.16/0.37  fof(c_0_71, plain, ![X48, X49]:((k4_xboole_0(X48,k1_tarski(X49))!=X48|~r2_hidden(X49,X48))&(r2_hidden(X49,X48)|k4_xboole_0(X48,k1_tarski(X49))=X48)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_zfmisc_1])])])).
% 0.16/0.37  fof(c_0_72, plain, ![X10, X11]:k4_xboole_0(X10,X11)=k5_xboole_0(X10,k3_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.16/0.37  fof(c_0_73, plain, ![X46, X47]:((k2_zfmisc_1(X46,X47)!=k1_xboole_0|(X46=k1_xboole_0|X47=k1_xboole_0))&((X46!=k1_xboole_0|k2_zfmisc_1(X46,X47)=k1_xboole_0)&(X47!=k1_xboole_0|k2_zfmisc_1(X46,X47)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.16/0.37  cnf(c_0_74, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_relat_1(esk4_0)|~r1_tarski(k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,esk3_0),k2_relat_1(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_61]), c_0_62])])).
% 0.16/0.37  cnf(c_0_75, negated_conjecture, (k7_relset_1(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),esk2_0,esk4_0,X1)=k9_relat_1(esk4_0,X1)), inference(spm,[status(thm)],[c_0_63, c_0_53])).
% 0.16/0.37  cnf(c_0_76, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.16/0.37  cnf(c_0_77, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.16/0.37  cnf(c_0_78, plain, (v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_66])).
% 0.16/0.37  cnf(c_0_79, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.16/0.37  cnf(c_0_80, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_62])])).
% 0.16/0.37  cnf(c_0_81, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.16/0.37  cnf(c_0_82, plain, (r2_hidden(X1,X2)|k4_xboole_0(X2,k1_tarski(X1))=X2), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.16/0.37  cnf(c_0_83, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.16/0.37  fof(c_0_84, plain, ![X12, X13]:(~r1_tarski(X12,X13)|k3_xboole_0(X12,X13)=X12), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 0.16/0.37  fof(c_0_85, plain, ![X15]:k5_xboole_0(X15,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t92_xboole_1])).
% 0.16/0.37  cnf(c_0_86, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.16/0.37  cnf(c_0_87, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_relat_1(esk4_0)|~r1_tarski(k9_relat_1(esk4_0,esk3_0),k2_relat_1(esk4_0))), inference(rw,[status(thm)],[c_0_74, c_0_75])).
% 0.16/0.37  cnf(c_0_88, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X3))|~v1_relat_1(X3)|~v1_relat_1(X1)|~r1_tarski(k7_relat_1(X1,X2),X3)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])).
% 0.16/0.37  cnf(c_0_89, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_relat_1(esk4_0)|~r1_tarski(k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0),k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_79, c_0_80])).
% 0.16/0.37  cnf(c_0_90, plain, (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.16/0.37  cnf(c_0_91, plain, (k5_xboole_0(X2,k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))=X2|r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_41]), c_0_42]), c_0_83]), c_0_43]), c_0_44]), c_0_45]), c_0_46]), c_0_47])).
% 0.16/0.37  cnf(c_0_92, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.16/0.37  cnf(c_0_93, plain, (k5_xboole_0(X1,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_85])).
% 0.16/0.37  fof(c_0_94, plain, ![X60, X61]:(~v1_relat_1(X61)|~v4_relat_1(X61,X60)|X61=k7_relat_1(X61,X60)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t209_relat_1])])).
% 0.16/0.37  cnf(c_0_95, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_86])).
% 0.16/0.37  cnf(c_0_96, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.16/0.37  cnf(c_0_97, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)!=k1_relat_1(esk4_0)|~r1_tarski(k7_relat_1(esk4_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_62])])).
% 0.16/0.37  cnf(c_0_98, negated_conjecture, (k6_enumset1(esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0,esk1_0)=k1_relat_1(esk4_0)|~r2_hidden(esk1_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.16/0.37  cnf(c_0_99, plain, (k1_xboole_0=X1|r2_hidden(X2,X1)|~r1_tarski(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_93])).
% 0.16/0.37  cnf(c_0_100, plain, (X1=k7_relat_1(X1,X2)|~v1_relat_1(X1)|~v4_relat_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_94])).
% 0.16/0.37  cnf(c_0_101, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.16/0.37  cnf(c_0_102, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_54, c_0_95])).
% 0.16/0.37  fof(c_0_103, plain, ![X14]:r1_tarski(k1_xboole_0,X14), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.16/0.37  cnf(c_0_104, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_96])).
% 0.16/0.37  cnf(c_0_105, negated_conjecture, (~r2_hidden(esk1_0,k1_relat_1(esk4_0))|~r1_tarski(k7_relat_1(esk4_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_97, c_0_98])).
% 0.16/0.37  cnf(c_0_106, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|r2_hidden(esk1_0,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_99, c_0_80])).
% 0.16/0.37  fof(c_0_107, plain, ![X65, X66]:(~v1_relat_1(X66)|r1_tarski(k7_relat_1(X66,X65),X66)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.16/0.37  cnf(c_0_108, negated_conjecture, (~r1_tarski(k9_relat_1(esk4_0,esk3_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))), inference(rw,[status(thm)],[c_0_59, c_0_75])).
% 0.16/0.37  cnf(c_0_109, plain, (k9_relat_1(X1,X2)=k2_relat_1(X1)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_77, c_0_100])).
% 0.16/0.37  cnf(c_0_110, plain, (r1_tarski(k2_relat_1(X1),k1_xboole_0)|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_101]), c_0_102])])).
% 0.16/0.37  cnf(c_0_111, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_103])).
% 0.16/0.37  cnf(c_0_112, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_58, c_0_104])).
% 0.16/0.37  fof(c_0_113, plain, ![X62]:(~v1_relat_1(X62)|r1_tarski(X62,k2_zfmisc_1(k1_relat_1(X62),k2_relat_1(X62)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_relat_1])])).
% 0.16/0.37  cnf(c_0_114, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0|~r1_tarski(k7_relat_1(esk4_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 0.16/0.37  cnf(c_0_115, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.16/0.37  cnf(c_0_116, negated_conjecture, (~v4_relat_1(esk4_0,esk3_0)|~r1_tarski(k2_relat_1(esk4_0),k6_enumset1(k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0),k1_funct_1(esk4_0,esk1_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_62])])).
% 0.16/0.37  cnf(c_0_117, plain, (k2_relat_1(X1)=k1_xboole_0|~v1_relat_1(X1)|~r1_tarski(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_110]), c_0_111])])).
% 0.16/0.37  cnf(c_0_118, plain, (v4_relat_1(X1,X2)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_112, c_0_66])).
% 0.16/0.37  cnf(c_0_119, plain, (r1_tarski(X1,k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_113])).
% 0.16/0.37  cnf(c_0_120, negated_conjecture, (k1_relat_1(esk4_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114, c_0_115]), c_0_62])])).
% 0.16/0.37  cnf(c_0_121, negated_conjecture, (~r1_tarski(esk4_0,k1_xboole_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116, c_0_117]), c_0_111]), c_0_62])]), c_0_118])).
% 0.16/0.37  cnf(c_0_122, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119, c_0_120]), c_0_95]), c_0_62])]), c_0_121]), ['proof']).
% 0.16/0.37  # SZS output end CNFRefutation
% 0.16/0.37  # Proof object total steps             : 123
% 0.16/0.37  # Proof object clause steps            : 65
% 0.16/0.37  # Proof object formula steps           : 58
% 0.16/0.37  # Proof object conjectures             : 25
% 0.16/0.37  # Proof object clause conjectures      : 22
% 0.16/0.37  # Proof object formula conjectures     : 3
% 0.16/0.37  # Proof object initial clauses used    : 32
% 0.16/0.37  # Proof object initial formulas used   : 29
% 0.16/0.37  # Proof object generating inferences   : 24
% 0.16/0.37  # Proof object simplifying inferences  : 81
% 0.16/0.37  # Training examples: 0 positive, 0 negative
% 0.16/0.37  # Parsed axioms                        : 29
% 0.16/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.16/0.37  # Initial clauses                      : 44
% 0.16/0.37  # Removed in clause preprocessing      : 8
% 0.16/0.37  # Initial clauses in saturation        : 36
% 0.16/0.37  # Processed clauses                    : 310
% 0.16/0.37  # ...of these trivial                  : 1
% 0.16/0.37  # ...subsumed                          : 111
% 0.16/0.37  # ...remaining for further processing  : 198
% 0.16/0.37  # Other redundant clauses eliminated   : 8
% 0.16/0.37  # Clauses deleted for lack of memory   : 0
% 0.16/0.37  # Backward-subsumed                    : 11
% 0.16/0.37  # Backward-rewritten                   : 40
% 0.16/0.37  # Generated clauses                    : 460
% 0.16/0.37  # ...of the previous two non-trivial   : 391
% 0.16/0.37  # Contextual simplify-reflections      : 12
% 0.16/0.37  # Paramodulations                      : 452
% 0.16/0.37  # Factorizations                       : 0
% 0.16/0.37  # Equation resolutions                 : 8
% 0.16/0.37  # Propositional unsat checks           : 0
% 0.16/0.37  #    Propositional check models        : 0
% 0.16/0.37  #    Propositional check unsatisfiable : 0
% 0.16/0.37  #    Propositional clauses             : 0
% 0.16/0.37  #    Propositional clauses after purity: 0
% 0.16/0.37  #    Propositional unsat core size     : 0
% 0.16/0.37  #    Propositional preprocessing time  : 0.000
% 0.16/0.37  #    Propositional encoding time       : 0.000
% 0.16/0.37  #    Propositional solver time         : 0.000
% 0.16/0.37  #    Success case prop preproc time    : 0.000
% 0.16/0.37  #    Success case prop encoding time   : 0.000
% 0.16/0.37  #    Success case prop solver time     : 0.000
% 0.16/0.37  # Current number of processed clauses  : 108
% 0.16/0.37  #    Positive orientable unit clauses  : 26
% 0.16/0.37  #    Positive unorientable unit clauses: 0
% 0.16/0.37  #    Negative unit clauses             : 4
% 0.16/0.37  #    Non-unit-clauses                  : 78
% 0.16/0.37  # Current number of unprocessed clauses: 112
% 0.16/0.37  # ...number of literals in the above   : 525
% 0.16/0.37  # Current number of archived formulas  : 0
% 0.16/0.37  # Current number of archived clauses   : 94
% 0.16/0.37  # Clause-clause subsumption calls (NU) : 4506
% 0.16/0.37  # Rec. Clause-clause subsumption calls : 1637
% 0.16/0.37  # Non-unit clause-clause subsumptions  : 83
% 0.16/0.37  # Unit Clause-clause subsumption calls : 53
% 0.16/0.37  # Rewrite failures with RHS unbound    : 0
% 0.16/0.37  # BW rewrite match attempts            : 3
% 0.16/0.37  # BW rewrite match successes           : 2
% 0.16/0.37  # Condensation attempts                : 0
% 0.16/0.37  # Condensation successes               : 0
% 0.16/0.37  # Termbank termtop insertions          : 10552
% 0.16/0.37  
% 0.16/0.37  # -------------------------------------------------
% 0.16/0.37  # User time                : 0.051 s
% 0.16/0.37  # System time              : 0.004 s
% 0.16/0.37  # Total time               : 0.055 s
% 0.16/0.37  # Maximum resident set size: 1608 pages
%------------------------------------------------------------------------------
