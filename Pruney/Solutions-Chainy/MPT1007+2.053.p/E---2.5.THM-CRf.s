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
% DateTime   : Thu Dec  3 11:04:21 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 193 expanded)
%              Number of clauses        :   44 (  79 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  230 ( 460 expanded)
%              Number of equality atoms :   60 ( 150 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,k1_tarski(X1),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
     => ( X2 != k1_xboole_0
       => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t128_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))
    <=> ( X1 = X3
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t172_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X2,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k1_relat_1(X2))
         => r2_hidden(k1_funct_1(X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t8_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( r2_hidden(k4_tarski(X1,X2),X3)
      <=> ( r2_hidden(X1,k1_relat_1(X3))
          & X2 = k1_funct_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(t56_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ! [X2,X3] : ~ r2_hidden(k4_tarski(X2,X3),X1)
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

fof(t22_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
     => ( ! [X4] :
            ~ ( r2_hidden(X4,X2)
              & ! [X5] : ~ r2_hidden(k4_tarski(X4,X5),X3) )
      <=> k1_relset_1(X2,X1,X3) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(fc3_xboole_0,axiom,(
    ! [X1,X2] : ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X7] : k2_tarski(X7,X7) = k1_tarski(X7) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k2_tarski(X8,X9) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X10,X11,X12] : k2_enumset1(X10,X10,X11,X12) = k1_enumset1(X10,X11,X12) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X15,X16,X17,X18] :
      ( ( X15 = X17
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),X18)) )
      & ( r2_hidden(X16,X18)
        | ~ r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),X18)) )
      & ( X15 != X17
        | ~ r2_hidden(X16,X18)
        | r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X44,X45,X46] :
      ( ( v4_relat_1(X46,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v5_relat_1(X46,X45)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_31,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | v1_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_32,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29])).

fof(c_0_35,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_relat_1(X34)
      | ~ v5_relat_1(X34,X33)
      | ~ v1_funct_1(X34)
      | ~ r2_hidden(X35,k1_relat_1(X34))
      | r2_hidden(k1_funct_1(X34,X35),X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).

cnf(c_0_36,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_38,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ r1_tarski(X40,X39) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_39,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_40,plain,(
    ! [X36,X37,X38] :
      ( ( r2_hidden(X36,k1_relat_1(X38))
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( X37 = k1_funct_1(X38,X36)
        | ~ r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( ~ r2_hidden(X36,k1_relat_1(X38))
        | X37 != k1_funct_1(X38,X36)
        | r2_hidden(k4_tarski(X36,X37),X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).

fof(c_0_41,plain,(
    ! [X30] :
      ( ~ v1_relat_1(X30)
      | r2_hidden(k4_tarski(esk2_1(X30),esk3_1(X30)),X30)
      | X30 = k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_44,plain,
    ( r2_hidden(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_45,negated_conjecture,
    ( v5_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_34])).

cnf(c_0_46,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_34])).

cnf(c_0_48,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_50,plain,(
    ! [X47,X48,X49,X51,X52] :
      ( ( r2_hidden(esk4_3(X47,X48,X49),X48)
        | k1_relset_1(X48,X47,X49) = X48
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X47))) )
      & ( ~ r2_hidden(k4_tarski(esk4_3(X47,X48,X49),X51),X49)
        | k1_relset_1(X48,X47,X49) = X48
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X47))) )
      & ( k1_relset_1(X48,X47,X49) != X48
        | ~ r2_hidden(X52,X48)
        | r2_hidden(k4_tarski(X52,esk5_4(X47,X48,X49,X52)),X49)
        | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).

fof(c_0_51,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_52,plain,(
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

cnf(c_0_53,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)
    | X1 = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_55,negated_conjecture,
    ( X1 = esk6_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk8_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_47])])).

cnf(c_0_58,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_59,plain,
    ( r2_hidden(k4_tarski(X4,esk5_4(X2,X1,X3,X4)),X3)
    | k1_relset_1(X1,X2,X3) != X1
    | ~ r2_hidden(X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_61,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_63,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( esk2_1(esk8_0) = esk6_0
    | esk8_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_54]),c_0_47])])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) != X1
    | ~ r2_hidden(X3,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_67,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = X1
    | X2 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X1,X2) ),
    inference(spm,[status(thm)],[c_0_61,c_0_60])).

cnf(c_0_68,negated_conjecture,
    ( v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_27]),c_0_28]),c_0_29])).

cnf(c_0_69,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_46]),c_0_47])]),c_0_65])).

fof(c_0_70,plain,(
    ! [X25,X26] :
      ( ~ m1_subset_1(X25,X26)
      | v1_xboole_0(X26)
      | r2_hidden(X25,X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_71,plain,(
    ! [X19] : m1_subset_1(esk1_1(X19),X19) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_72,plain,(
    ! [X13,X14] : ~ v1_xboole_0(k2_tarski(X13,X14)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ v1_funct_2(k1_xboole_0,X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk1_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])).

cnf(c_0_80,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78,c_0_28]),c_0_29])).

cnf(c_0_82,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.48  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.20/0.48  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.48  #
% 0.20/0.48  # Preprocessing time       : 0.034 s
% 0.20/0.48  
% 0.20/0.48  # Proof found!
% 0.20/0.48  # SZS status Theorem
% 0.20/0.48  # SZS output start CNFRefutation
% 0.20/0.48  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 0.20/0.48  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.48  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.48  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.48  fof(t128_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),X4))<=>(X1=X3&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 0.20/0.48  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.20/0.48  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.48  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.20/0.48  fof(t172_funct_1, axiom, ![X1, X2]:(((v1_relat_1(X2)&v5_relat_1(X2,X1))&v1_funct_1(X2))=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 0.20/0.48  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.48  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.48  fof(t8_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>(r2_hidden(k4_tarski(X1,X2),X3)<=>(r2_hidden(X1,k1_relat_1(X3))&X2=k1_funct_1(X3,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 0.20/0.48  fof(t56_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(![X2, X3]:~(r2_hidden(k4_tarski(X2,X3),X1))=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 0.20/0.48  fof(t22_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>(![X4]:~((r2_hidden(X4,X2)&![X5]:~(r2_hidden(k4_tarski(X4,X5),X3))))<=>k1_relset_1(X2,X1,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 0.20/0.48  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.48  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.48  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.48  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.20/0.48  fof(fc3_xboole_0, axiom, ![X1, X2]:~(v1_xboole_0(k2_tarski(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 0.20/0.48  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.20/0.48  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.20/0.48  fof(c_0_21, plain, ![X7]:k2_tarski(X7,X7)=k1_tarski(X7), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.48  fof(c_0_22, plain, ![X8, X9]:k1_enumset1(X8,X8,X9)=k2_tarski(X8,X9), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.48  fof(c_0_23, plain, ![X10, X11, X12]:k2_enumset1(X10,X10,X11,X12)=k1_enumset1(X10,X11,X12), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.48  fof(c_0_24, plain, ![X15, X16, X17, X18]:(((X15=X17|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),X18)))&(r2_hidden(X16,X18)|~r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),X18))))&(X15!=X17|~r2_hidden(X16,X18)|r2_hidden(k4_tarski(X15,X16),k2_zfmisc_1(k1_tarski(X17),X18)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t128_zfmisc_1])])])).
% 0.20/0.48  fof(c_0_25, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.20/0.48  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_27, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.48  cnf(c_0_28, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.48  cnf(c_0_29, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.48  fof(c_0_30, plain, ![X44, X45, X46]:((v4_relat_1(X46,X44)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(v5_relat_1(X46,X45)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.48  fof(c_0_31, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|v1_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.20/0.48  cnf(c_0_32, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),X4))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.48  cnf(c_0_33, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.48  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.48  fof(c_0_35, plain, ![X33, X34, X35]:(~v1_relat_1(X34)|~v5_relat_1(X34,X33)|~v1_funct_1(X34)|(~r2_hidden(X35,k1_relat_1(X34))|r2_hidden(k1_funct_1(X34,X35),X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t172_funct_1])])])).
% 0.20/0.48  cnf(c_0_36, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.48  cnf(c_0_37, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.48  fof(c_0_38, plain, ![X39, X40]:(~r2_hidden(X39,X40)|~r1_tarski(X40,X39)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.48  fof(c_0_39, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.48  fof(c_0_40, plain, ![X36, X37, X38]:(((r2_hidden(X36,k1_relat_1(X38))|~r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(X37=k1_funct_1(X38,X36)|~r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38))))&(~r2_hidden(X36,k1_relat_1(X38))|X37!=k1_funct_1(X38,X36)|r2_hidden(k4_tarski(X36,X37),X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_funct_1])])])).
% 0.20/0.48  fof(c_0_41, plain, ![X30]:(~v1_relat_1(X30)|(r2_hidden(k4_tarski(esk2_1(X30),esk3_1(X30)),X30)|X30=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t56_relat_1])])])])).
% 0.20/0.48  cnf(c_0_42, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.48  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.48  cnf(c_0_44, plain, (r2_hidden(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.48  cnf(c_0_45, negated_conjecture, (v5_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_36, c_0_34])).
% 0.20/0.48  cnf(c_0_46, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_34])).
% 0.20/0.48  cnf(c_0_48, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.48  cnf(c_0_49, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.48  fof(c_0_50, plain, ![X47, X48, X49, X51, X52]:(((r2_hidden(esk4_3(X47,X48,X49),X48)|k1_relset_1(X48,X47,X49)=X48|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X47))))&(~r2_hidden(k4_tarski(esk4_3(X47,X48,X49),X51),X49)|k1_relset_1(X48,X47,X49)=X48|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X47)))))&(k1_relset_1(X48,X47,X49)!=X48|(~r2_hidden(X52,X48)|r2_hidden(k4_tarski(X52,esk5_4(X47,X48,X49,X52)),X49))|~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(X48,X47))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_relset_1])])])])])])).
% 0.20/0.48  fof(c_0_51, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.48  fof(c_0_52, plain, ![X54, X55, X56]:((((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&((~v1_funct_2(X56,X54,X55)|X56=k1_xboole_0|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X56!=k1_xboole_0|v1_funct_2(X56,X54,X55)|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.48  cnf(c_0_53, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.48  cnf(c_0_54, plain, (r2_hidden(k4_tarski(esk2_1(X1),esk3_1(X1)),X1)|X1=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.48  cnf(c_0_55, negated_conjecture, (X1=esk6_0|~r2_hidden(k4_tarski(X1,X2),esk8_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.48  cnf(c_0_56, negated_conjecture, (~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_57, negated_conjecture, (r2_hidden(k1_funct_1(esk8_0,X1),esk7_0)|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_47])])).
% 0.20/0.48  cnf(c_0_58, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.48  cnf(c_0_59, plain, (r2_hidden(k4_tarski(X4,esk5_4(X2,X1,X3,X4)),X3)|k1_relset_1(X1,X2,X3)!=X1|~r2_hidden(X4,X1)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.48  cnf(c_0_60, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.48  cnf(c_0_61, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.48  cnf(c_0_62, negated_conjecture, (v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_63, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.48  cnf(c_0_64, negated_conjecture, (esk2_1(esk8_0)=esk6_0|esk8_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_54]), c_0_47])])).
% 0.20/0.48  cnf(c_0_65, negated_conjecture, (~r2_hidden(esk6_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.48  cnf(c_0_66, plain, (k1_relset_1(X1,X2,k1_xboole_0)!=X1|~r2_hidden(X3,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 0.20/0.48  cnf(c_0_67, plain, (k1_relset_1(X1,X2,k1_xboole_0)=X1|X2=k1_xboole_0|~v1_funct_2(k1_xboole_0,X1,X2)), inference(spm,[status(thm)],[c_0_61, c_0_60])).
% 0.20/0.48  cnf(c_0_68, negated_conjecture, (v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_62, c_0_27]), c_0_28]), c_0_29])).
% 0.20/0.48  cnf(c_0_69, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_46]), c_0_47])]), c_0_65])).
% 0.20/0.48  fof(c_0_70, plain, ![X25, X26]:(~m1_subset_1(X25,X26)|(v1_xboole_0(X26)|r2_hidden(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.48  fof(c_0_71, plain, ![X19]:m1_subset_1(esk1_1(X19),X19), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.20/0.48  fof(c_0_72, plain, ![X13, X14]:~v1_xboole_0(k2_tarski(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc3_xboole_0])])).
% 0.20/0.48  cnf(c_0_73, plain, (X1=k1_xboole_0|~v1_funct_2(k1_xboole_0,X2,X1)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.48  cnf(c_0_74, negated_conjecture, (v1_funct_2(k1_xboole_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[c_0_68, c_0_69])).
% 0.20/0.48  cnf(c_0_75, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.48  cnf(c_0_76, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.20/0.48  cnf(c_0_77, plain, (m1_subset_1(esk1_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_71])).
% 0.20/0.48  cnf(c_0_78, plain, (~v1_xboole_0(k2_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.48  cnf(c_0_79, negated_conjecture, (~r2_hidden(X1,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_75])).
% 0.20/0.48  cnf(c_0_80, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.48  cnf(c_0_81, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_78, c_0_28]), c_0_29])).
% 0.20/0.48  cnf(c_0_82, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81]), ['proof']).
% 0.20/0.48  # SZS output end CNFRefutation
% 0.20/0.48  # Proof object total steps             : 83
% 0.20/0.48  # Proof object clause steps            : 44
% 0.20/0.48  # Proof object formula steps           : 39
% 0.20/0.48  # Proof object conjectures             : 21
% 0.20/0.48  # Proof object clause conjectures      : 18
% 0.20/0.48  # Proof object formula conjectures     : 3
% 0.20/0.48  # Proof object initial clauses used    : 23
% 0.20/0.48  # Proof object initial formulas used   : 19
% 0.20/0.48  # Proof object generating inferences   : 16
% 0.20/0.48  # Proof object simplifying inferences  : 25
% 0.20/0.48  # Training examples: 0 positive, 0 negative
% 0.20/0.48  # Parsed axioms                        : 20
% 0.20/0.48  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.48  # Initial clauses                      : 36
% 0.20/0.48  # Removed in clause preprocessing      : 3
% 0.20/0.48  # Initial clauses in saturation        : 33
% 0.20/0.48  # Processed clauses                    : 174
% 0.20/0.48  # ...of these trivial                  : 1
% 0.20/0.48  # ...subsumed                          : 19
% 0.20/0.48  # ...remaining for further processing  : 154
% 0.20/0.48  # Other redundant clauses eliminated   : 7
% 0.20/0.48  # Clauses deleted for lack of memory   : 0
% 0.20/0.48  # Backward-subsumed                    : 3
% 0.20/0.48  # Backward-rewritten                   : 18
% 0.20/0.48  # Generated clauses                    : 481
% 0.20/0.48  # ...of the previous two non-trivial   : 482
% 0.20/0.48  # Contextual simplify-reflections      : 0
% 0.20/0.48  # Paramodulations                      : 475
% 0.20/0.48  # Factorizations                       : 0
% 0.20/0.48  # Equation resolutions                 : 7
% 0.20/0.48  # Propositional unsat checks           : 0
% 0.20/0.48  #    Propositional check models        : 0
% 0.20/0.48  #    Propositional check unsatisfiable : 0
% 0.20/0.48  #    Propositional clauses             : 0
% 0.20/0.48  #    Propositional clauses after purity: 0
% 0.20/0.48  #    Propositional unsat core size     : 0
% 0.20/0.48  #    Propositional preprocessing time  : 0.000
% 0.20/0.48  #    Propositional encoding time       : 0.000
% 0.20/0.48  #    Propositional solver time         : 0.000
% 0.20/0.48  #    Success case prop preproc time    : 0.000
% 0.20/0.48  #    Success case prop encoding time   : 0.000
% 0.20/0.48  #    Success case prop solver time     : 0.000
% 0.20/0.48  # Current number of processed clauses  : 127
% 0.20/0.48  #    Positive orientable unit clauses  : 28
% 0.20/0.48  #    Positive unorientable unit clauses: 0
% 0.20/0.48  #    Negative unit clauses             : 7
% 0.20/0.48  #    Non-unit-clauses                  : 92
% 0.20/0.48  # Current number of unprocessed clauses: 326
% 0.20/0.48  # ...number of literals in the above   : 4593
% 0.20/0.48  # Current number of archived formulas  : 0
% 0.20/0.48  # Current number of archived clauses   : 24
% 0.20/0.48  # Clause-clause subsumption calls (NU) : 6264
% 0.20/0.48  # Rec. Clause-clause subsumption calls : 349
% 0.20/0.48  # Non-unit clause-clause subsumptions  : 10
% 0.20/0.48  # Unit Clause-clause subsumption calls : 116
% 0.20/0.48  # Rewrite failures with RHS unbound    : 0
% 0.20/0.48  # BW rewrite match attempts            : 72
% 0.20/0.48  # BW rewrite match successes           : 3
% 0.20/0.48  # Condensation attempts                : 0
% 0.20/0.48  # Condensation successes               : 0
% 0.20/0.48  # Termbank termtop insertions          : 53447
% 0.20/0.48  
% 0.20/0.48  # -------------------------------------------------
% 0.20/0.48  # User time                : 0.126 s
% 0.20/0.48  # System time              : 0.007 s
% 0.20/0.48  # Total time               : 0.133 s
% 0.20/0.48  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
