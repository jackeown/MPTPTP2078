%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:16 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 272 expanded)
%              Number of clauses        :   37 ( 108 expanded)
%              Number of leaves         :   15 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 ( 764 expanded)
%              Number of equality atoms :   81 ( 321 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   28 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

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

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t176_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v5_relat_1(X3,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,k1_relat_1(X3))
       => m1_subset_1(k1_funct_1(X3,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,k1_tarski(X1),X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r2_hidden(k1_funct_1(X3,X1),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t61_funct_2])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))
    & esk7_0 != k1_xboole_0
    & ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_17,plain,(
    ! [X21] : k2_tarski(X21,X21) = k1_tarski(X21) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X22,X23] : k1_enumset1(X22,X22,X23) = k2_tarski(X22,X23) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_19,plain,(
    ! [X24,X25,X26] : k2_enumset1(X24,X24,X25,X26) = k1_enumset1(X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X10,X11,X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( ~ r2_hidden(X14,X13)
        | X14 = X10
        | X14 = X11
        | X14 = X12
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X10
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X11
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( X15 != X12
        | r2_hidden(X15,X13)
        | X13 != k1_enumset1(X10,X11,X12) )
      & ( esk2_4(X16,X17,X18,X19) != X16
        | ~ r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( esk2_4(X16,X17,X18,X19) != X17
        | ~ r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( esk2_4(X16,X17,X18,X19) != X18
        | ~ r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | X19 = k1_enumset1(X16,X17,X18) )
      & ( r2_hidden(esk2_4(X16,X17,X18,X19),X19)
        | esk2_4(X16,X17,X18,X19) = X16
        | esk2_4(X16,X17,X18,X19) = X17
        | esk2_4(X16,X17,X18,X19) = X18
        | X19 = k1_enumset1(X16,X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_21,plain,(
    ! [X52,X53,X54] :
      ( ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k1_relset_1(X52,X53,X54) = k1_relat_1(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
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

cnf(c_0_28,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_31,plain,(
    ! [X37,X38,X39] :
      ( ( X39 != k1_funct_1(X37,X38)
        | r2_hidden(k4_tarski(X38,X39),X37)
        | ~ r2_hidden(X38,k1_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( ~ r2_hidden(k4_tarski(X38,X39),X37)
        | X39 = k1_funct_1(X37,X38)
        | ~ r2_hidden(X38,k1_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( X39 != k1_funct_1(X37,X38)
        | X39 = k1_xboole_0
        | r2_hidden(X38,k1_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) )
      & ( X39 != k1_xboole_0
        | X39 = k1_funct_1(X37,X38)
        | r2_hidden(X38,k1_relat_1(X37))
        | ~ v1_relat_1(X37)
        | ~ v1_funct_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_32,plain,(
    ! [X6,X7,X8] :
      ( ( ~ v1_xboole_0(X6)
        | ~ r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_1(X8),X8)
        | v1_xboole_0(X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_33,plain,(
    ! [X29,X30,X33,X35,X36] :
      ( ( ~ v1_relat_1(X29)
        | ~ r2_hidden(X30,X29)
        | X30 = k4_tarski(esk3_2(X29,X30),esk4_2(X29,X30)) )
      & ( r2_hidden(esk5_1(X33),X33)
        | v1_relat_1(X33) )
      & ( esk5_1(X33) != k4_tarski(X35,X36)
        | v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X4,X5) ),
    inference(rw,[status(thm)],[c_0_26,c_0_25])).

cnf(c_0_35,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( k1_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_23]),c_0_24]),c_0_25])).

cnf(c_0_38,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_39,plain,(
    ! [X43,X44,X45] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | v1_relat_1(X45) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X3,X1),X2)
    | X1 != k1_funct_1(X2,X3)
    | ~ r2_hidden(X3,k1_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_43,plain,(
    ! [X40,X41,X42] :
      ( ~ v1_relat_1(X42)
      | ~ v5_relat_1(X42,X40)
      | ~ v1_funct_1(X42)
      | ~ r2_hidden(X41,k1_relat_1(X42))
      | m1_subset_1(k1_funct_1(X42,X41),X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_45,negated_conjecture,
    ( k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0) = k1_relat_1(esk8_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_36]),c_0_37])]),c_0_38])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_47,plain,(
    ! [X46,X47,X48] :
      ( ( v4_relat_1(X48,X46)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) )
      & ( v5_relat_1(X48,X47)
        | ~ m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_40])).

cnf(c_0_49,plain,
    ( v1_relat_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_funct_1(X1,X3),X2)
    | ~ v1_relat_1(X1)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk6_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_29])).

cnf(c_0_54,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_55,plain,(
    ! [X49,X50,X51] :
      ( ~ v1_xboole_0(X49)
      | ~ m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))
      | v1_xboole_0(X51) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_56,plain,
    ( ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_48]),c_0_49])).

fof(c_0_57,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk8_0,esk6_0),X1)
    | ~ v5_relat_1(esk8_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52]),c_0_53])])).

cnf(c_0_59,negated_conjecture,
    ( v5_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_29])).

cnf(c_0_60,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),esk7_0))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_45])).

cnf(c_0_62,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_51]),c_0_52])])).

cnf(c_0_63,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_66,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.053 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t61_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 0.13/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 0.13/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 0.13/0.40  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 0.13/0.40  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.13/0.40  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 0.13/0.40  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 0.13/0.40  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.13/0.40  fof(t176_funct_1, axiom, ![X1, X2, X3]:(((v1_relat_1(X3)&v5_relat_1(X3,X1))&v1_funct_1(X3))=>(r2_hidden(X2,k1_relat_1(X3))=>m1_subset_1(k1_funct_1(X3,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 0.13/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.13/0.40  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.13/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.40  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,k1_tarski(X1),X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r2_hidden(k1_funct_1(X3,X1),X2)))), inference(assume_negation,[status(cth)],[t61_funct_2])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0))))&(esk7_0!=k1_xboole_0&~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X21]:k2_tarski(X21,X21)=k1_tarski(X21), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.40  fof(c_0_18, plain, ![X22, X23]:k1_enumset1(X22,X22,X23)=k2_tarski(X22,X23), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.13/0.40  fof(c_0_19, plain, ![X24, X25, X26]:k2_enumset1(X24,X24,X25,X26)=k1_enumset1(X24,X25,X26), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.13/0.40  fof(c_0_20, plain, ![X10, X11, X12, X13, X14, X15, X16, X17, X18, X19]:(((~r2_hidden(X14,X13)|(X14=X10|X14=X11|X14=X12)|X13!=k1_enumset1(X10,X11,X12))&(((X15!=X10|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12))&(X15!=X11|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12)))&(X15!=X12|r2_hidden(X15,X13)|X13!=k1_enumset1(X10,X11,X12))))&((((esk2_4(X16,X17,X18,X19)!=X16|~r2_hidden(esk2_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18))&(esk2_4(X16,X17,X18,X19)!=X17|~r2_hidden(esk2_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18)))&(esk2_4(X16,X17,X18,X19)!=X18|~r2_hidden(esk2_4(X16,X17,X18,X19),X19)|X19=k1_enumset1(X16,X17,X18)))&(r2_hidden(esk2_4(X16,X17,X18,X19),X19)|(esk2_4(X16,X17,X18,X19)=X16|esk2_4(X16,X17,X18,X19)=X17|esk2_4(X16,X17,X18,X19)=X18)|X19=k1_enumset1(X16,X17,X18)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.13/0.40  fof(c_0_21, plain, ![X52, X53, X54]:(~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k1_relset_1(X52,X53,X54)=k1_relat_1(X54)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk6_0),esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_23, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_24, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_25, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  fof(c_0_27, plain, ![X55, X56, X57]:((((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X56=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))&((~v1_funct_2(X57,X55,X56)|X55=k1_relset_1(X55,X56,X57)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X55!=k1_relset_1(X55,X56,X57)|v1_funct_2(X57,X55,X56)|X55!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))))&((~v1_funct_2(X57,X55,X56)|X57=k1_xboole_0|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56))))&(X57!=k1_xboole_0|v1_funct_2(X57,X55,X56)|X55=k1_xboole_0|X56!=k1_xboole_0|~m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X55,X56)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.13/0.40  cnf(c_0_28, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_22, c_0_23]), c_0_24]), c_0_25])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk8_0,k1_tarski(esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  fof(c_0_31, plain, ![X37, X38, X39]:(((X39!=k1_funct_1(X37,X38)|r2_hidden(k4_tarski(X38,X39),X37)|~r2_hidden(X38,k1_relat_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(~r2_hidden(k4_tarski(X38,X39),X37)|X39=k1_funct_1(X37,X38)|~r2_hidden(X38,k1_relat_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37))))&((X39!=k1_funct_1(X37,X38)|X39=k1_xboole_0|r2_hidden(X38,k1_relat_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37)))&(X39!=k1_xboole_0|X39=k1_funct_1(X37,X38)|r2_hidden(X38,k1_relat_1(X37))|(~v1_relat_1(X37)|~v1_funct_1(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.13/0.41  fof(c_0_32, plain, ![X6, X7, X8]:((~v1_xboole_0(X6)|~r2_hidden(X7,X6))&(r2_hidden(esk1_1(X8),X8)|v1_xboole_0(X8))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.41  fof(c_0_33, plain, ![X29, X30, X33, X35, X36]:((~v1_relat_1(X29)|(~r2_hidden(X30,X29)|X30=k4_tarski(esk3_2(X29,X30),esk4_2(X29,X30))))&((r2_hidden(esk5_1(X33),X33)|v1_relat_1(X33))&(esk5_1(X33)!=k4_tarski(X35,X36)|v1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.13/0.41  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X4,X5)), inference(rw,[status(thm)],[c_0_26, c_0_25])).
% 0.13/0.41  cnf(c_0_35, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.41  cnf(c_0_36, negated_conjecture, (k1_relset_1(k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.41  cnf(c_0_37, negated_conjecture, (v1_funct_2(esk8_0,k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0),esk7_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_23]), c_0_24]), c_0_25])).
% 0.13/0.41  cnf(c_0_38, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  fof(c_0_39, plain, ![X43, X44, X45]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|v1_relat_1(X45)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.13/0.41  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X3,X1),X2)|X1!=k1_funct_1(X2,X3)|~r2_hidden(X3,k1_relat_1(X2))|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.41  cnf(c_0_41, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.41  cnf(c_0_42, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.13/0.41  fof(c_0_43, plain, ![X40, X41, X42]:(~v1_relat_1(X42)|~v5_relat_1(X42,X40)|~v1_funct_1(X42)|(~r2_hidden(X41,k1_relat_1(X42))|m1_subset_1(k1_funct_1(X42,X41),X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t176_funct_1])])).
% 0.13/0.41  cnf(c_0_44, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.13/0.41  cnf(c_0_45, negated_conjecture, (k2_enumset1(esk6_0,esk6_0,esk6_0,esk6_0)=k1_relat_1(esk8_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_29]), c_0_36]), c_0_37])]), c_0_38])).
% 0.13/0.41  cnf(c_0_46, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.41  fof(c_0_47, plain, ![X46, X47, X48]:((v4_relat_1(X48,X46)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))&(v5_relat_1(X48,X47)|~m1_subset_1(X48,k1_zfmisc_1(k2_zfmisc_1(X46,X47))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.13/0.41  cnf(c_0_48, plain, (r2_hidden(k4_tarski(X1,k1_funct_1(X2,X1)),X2)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_40])).
% 0.13/0.41  cnf(c_0_49, plain, (v1_relat_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.41  cnf(c_0_50, plain, (m1_subset_1(k1_funct_1(X1,X3),X2)|~v1_relat_1(X1)|~v5_relat_1(X1,X2)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.41  cnf(c_0_51, negated_conjecture, (r2_hidden(esk6_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.41  cnf(c_0_52, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_53, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_46, c_0_29])).
% 0.13/0.41  cnf(c_0_54, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.13/0.41  fof(c_0_55, plain, ![X49, X50, X51]:(~v1_xboole_0(X49)|(~m1_subset_1(X51,k1_zfmisc_1(k2_zfmisc_1(X50,X49)))|v1_xboole_0(X51))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.13/0.41  cnf(c_0_56, plain, (~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~v1_xboole_0(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_48]), c_0_49])).
% 0.13/0.41  fof(c_0_57, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.41  cnf(c_0_58, negated_conjecture, (m1_subset_1(k1_funct_1(esk8_0,esk6_0),X1)|~v5_relat_1(esk8_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52]), c_0_53])])).
% 0.13/0.41  cnf(c_0_59, negated_conjecture, (v5_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_54, c_0_29])).
% 0.13/0.41  cnf(c_0_60, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.13/0.41  cnf(c_0_61, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(esk8_0),esk7_0)))), inference(rw,[status(thm)],[c_0_29, c_0_45])).
% 0.13/0.41  cnf(c_0_62, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_51]), c_0_52])])).
% 0.13/0.41  cnf(c_0_63, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.13/0.41  cnf(c_0_64, negated_conjecture, (m1_subset_1(k1_funct_1(esk8_0,esk6_0),esk7_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.41  cnf(c_0_65, negated_conjecture, (~r2_hidden(k1_funct_1(esk8_0,esk6_0),esk7_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.41  cnf(c_0_66, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])).
% 0.13/0.41  cnf(c_0_67, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65]), c_0_66]), ['proof']).
% 0.13/0.41  # SZS output end CNFRefutation
% 0.13/0.41  # Proof object total steps             : 68
% 0.13/0.41  # Proof object clause steps            : 37
% 0.13/0.41  # Proof object formula steps           : 31
% 0.13/0.41  # Proof object conjectures             : 21
% 0.13/0.41  # Proof object clause conjectures      : 18
% 0.13/0.41  # Proof object formula conjectures     : 3
% 0.13/0.41  # Proof object initial clauses used    : 19
% 0.13/0.41  # Proof object initial formulas used   : 15
% 0.13/0.41  # Proof object generating inferences   : 12
% 0.13/0.41  # Proof object simplifying inferences  : 24
% 0.13/0.41  # Training examples: 0 positive, 0 negative
% 0.13/0.41  # Parsed axioms                        : 15
% 0.13/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.41  # Initial clauses                      : 38
% 0.13/0.41  # Removed in clause preprocessing      : 3
% 0.13/0.41  # Initial clauses in saturation        : 35
% 0.13/0.41  # Processed clauses                    : 113
% 0.13/0.41  # ...of these trivial                  : 3
% 0.13/0.41  # ...subsumed                          : 7
% 0.13/0.41  # ...remaining for further processing  : 103
% 0.13/0.41  # Other redundant clauses eliminated   : 16
% 0.13/0.41  # Clauses deleted for lack of memory   : 0
% 0.13/0.41  # Backward-subsumed                    : 0
% 0.13/0.41  # Backward-rewritten                   : 6
% 0.13/0.41  # Generated clauses                    : 73
% 0.13/0.41  # ...of the previous two non-trivial   : 70
% 0.13/0.41  # Contextual simplify-reflections      : 1
% 0.13/0.41  # Paramodulations                      : 61
% 0.13/0.41  # Factorizations                       : 0
% 0.13/0.41  # Equation resolutions                 : 16
% 0.13/0.41  # Propositional unsat checks           : 0
% 0.13/0.41  #    Propositional check models        : 0
% 0.13/0.41  #    Propositional check unsatisfiable : 0
% 0.13/0.41  #    Propositional clauses             : 0
% 0.13/0.41  #    Propositional clauses after purity: 0
% 0.13/0.41  #    Propositional unsat core size     : 0
% 0.13/0.41  #    Propositional preprocessing time  : 0.000
% 0.13/0.41  #    Propositional encoding time       : 0.000
% 0.13/0.41  #    Propositional solver time         : 0.000
% 0.13/0.41  #    Success case prop preproc time    : 0.000
% 0.13/0.41  #    Success case prop encoding time   : 0.000
% 0.13/0.41  #    Success case prop solver time     : 0.000
% 0.13/0.41  # Current number of processed clauses  : 52
% 0.13/0.41  #    Positive orientable unit clauses  : 14
% 0.13/0.41  #    Positive unorientable unit clauses: 0
% 0.13/0.41  #    Negative unit clauses             : 6
% 0.13/0.41  #    Non-unit-clauses                  : 32
% 0.13/0.41  # Current number of unprocessed clauses: 26
% 0.13/0.41  # ...number of literals in the above   : 98
% 0.13/0.41  # Current number of archived formulas  : 0
% 0.13/0.41  # Current number of archived clauses   : 43
% 0.13/0.41  # Clause-clause subsumption calls (NU) : 221
% 0.13/0.41  # Rec. Clause-clause subsumption calls : 100
% 0.13/0.41  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.41  # Unit Clause-clause subsumption calls : 58
% 0.13/0.41  # Rewrite failures with RHS unbound    : 0
% 0.13/0.41  # BW rewrite match attempts            : 7
% 0.13/0.41  # BW rewrite match successes           : 1
% 0.13/0.41  # Condensation attempts                : 0
% 0.13/0.41  # Condensation successes               : 0
% 0.13/0.41  # Termbank termtop insertions          : 3710
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.059 s
% 0.13/0.41  # System time              : 0.008 s
% 0.13/0.41  # Total time               : 0.067 s
% 0.13/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
