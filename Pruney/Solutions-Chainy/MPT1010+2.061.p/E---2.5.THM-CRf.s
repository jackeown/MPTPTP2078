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
% DateTime   : Thu Dec  3 11:05:20 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 161 expanded)
%              Number of clauses        :   39 (  68 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  230 ( 459 expanded)
%              Number of equality atoms :   90 ( 203 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(dt_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,k1_tarski(X2))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))) )
       => ( r2_hidden(X3,X1)
         => k1_funct_1(X4,X3) = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t65_funct_2])).

fof(c_0_16,plain,(
    ! [X42,X43,X44] :
      ( ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))
      | m1_subset_1(k2_relset_1(X42,X43,X44),k1_zfmisc_1(X43)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).

fof(c_0_17,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k2_relset_1(X48,X49,X50) = k2_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))
    & r2_hidden(esk8_0,esk6_0)
    & k1_funct_1(esk9_0,esk8_0) != esk7_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_19,plain,(
    ! [X18] : k2_tarski(X18,X18) = k1_tarski(X18) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X19,X20] : k1_enumset1(X19,X19,X20) = k2_tarski(X19,X20) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X21,X22,X23] : k2_enumset1(X21,X21,X22,X23) = k1_enumset1(X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X12,X13,X14,X15,X16] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X9
        | X12 = X10
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k2_tarski(X9,X10) )
      & ( esk2_3(X14,X15,X16) != X14
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( esk2_3(X14,X15,X16) != X15
        | ~ r2_hidden(esk2_3(X14,X15,X16),X16)
        | X16 = k2_tarski(X14,X15) )
      & ( r2_hidden(esk2_3(X14,X15,X16),X16)
        | esk2_3(X14,X15,X16) = X14
        | esk2_3(X14,X15,X16) = X15
        | X16 = k2_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_30,plain,(
    ! [X26,X27,X28] :
      ( ~ r2_hidden(X26,X27)
      | ~ m1_subset_1(X27,k1_zfmisc_1(X28))
      | m1_subset_1(X26,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_31,plain,
    ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_33,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X4,X4,X4,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_27]),c_0_28])).

fof(c_0_35,plain,(
    ! [X45,X46,X47] :
      ( ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))
      | k1_relset_1(X45,X46,X47) = k1_relat_1(X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_36,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_37,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,X25)
      | v1_xboole_0(X25)
      | r2_hidden(X24,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(k2_relat_1(esk9_0),k1_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,k2_enumset1(X2,X2,X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

fof(c_0_42,plain,(
    ! [X51,X52,X53] :
      ( ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X52 = k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X51 = k1_relset_1(X51,X52,X53)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_relset_1(X51,X52,X53)
        | v1_funct_2(X53,X51,X52)
        | X51 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( ~ v1_funct_2(X53,X51,X52)
        | X53 = k1_xboole_0
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X53 != k1_xboole_0
        | v1_funct_2(X53,X51,X52)
        | X51 = k1_xboole_0
        | X52 != k1_xboole_0
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_43,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k2_enumset1(X3,X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_27]),c_0_28])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( ~ v1_xboole_0(k2_enumset1(X1,X1,X1,X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

fof(c_0_49,plain,(
    ! [X29,X30,X31,X33,X34,X35,X37] :
      ( ( r2_hidden(esk3_3(X29,X30,X31),k1_relat_1(X29))
        | ~ r2_hidden(X31,X30)
        | X30 != k2_relat_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 = k1_funct_1(X29,esk3_3(X29,X30,X31))
        | ~ r2_hidden(X31,X30)
        | X30 != k2_relat_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(X34,k1_relat_1(X29))
        | X33 != k1_funct_1(X29,X34)
        | r2_hidden(X33,X30)
        | X30 != k2_relat_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(esk4_2(X29,X35),X35)
        | ~ r2_hidden(X37,k1_relat_1(X29))
        | esk4_2(X29,X35) != k1_funct_1(X29,X37)
        | X35 = k2_relat_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( r2_hidden(esk5_2(X29,X35),k1_relat_1(X29))
        | r2_hidden(esk4_2(X29,X35),X35)
        | X35 = k2_relat_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( esk4_2(X29,X35) = k1_funct_1(X29,esk5_2(X29,X35))
        | r2_hidden(esk4_2(X29,X35),X35)
        | X35 = k2_relat_1(X29)
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_50,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_51,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( k1_relset_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_32])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(esk9_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_54,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_enumset1(X3,X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])).

cnf(c_0_56,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0) = k1_xboole_0
    | k1_relat_1(esk9_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_32]),c_0_52]),c_0_53])])).

cnf(c_0_59,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_60,negated_conjecture,
    ( X1 = esk7_0
    | ~ r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_58]),c_0_59])])).

cnf(c_0_65,negated_conjecture,
    ( k1_funct_1(esk9_0,esk8_0) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_66,negated_conjecture,
    ( k1_funct_1(esk9_0,X1) = esk7_0
    | ~ r2_hidden(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_63]),c_0_64])])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk8_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.38  #
% 0.21/0.38  # Preprocessing time       : 0.029 s
% 0.21/0.38  # Presaturation interreduction done
% 0.21/0.38  
% 0.21/0.38  # Proof found!
% 0.21/0.38  # SZS status Theorem
% 0.21/0.38  # SZS output start CNFRefutation
% 0.21/0.38  fof(t65_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 0.21/0.38  fof(dt_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>m1_subset_1(k2_relset_1(X1,X2,X3),k1_zfmisc_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 0.21/0.38  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.21/0.38  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.38  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.38  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.38  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.38  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.21/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.21/0.38  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.21/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.21/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.21/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.21/0.38  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,k1_tarski(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k1_tarski(X2)))))=>(r2_hidden(X3,X1)=>k1_funct_1(X4,X3)=X2))), inference(assume_negation,[status(cth)],[t65_funct_2])).
% 0.21/0.38  fof(c_0_16, plain, ![X42, X43, X44]:(~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43)))|m1_subset_1(k2_relset_1(X42,X43,X44),k1_zfmisc_1(X43))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_relset_1])])).
% 0.21/0.38  fof(c_0_17, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k2_relset_1(X48,X49,X50)=k2_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.21/0.38  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0)))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0)))))&(r2_hidden(esk8_0,esk6_0)&k1_funct_1(esk9_0,esk8_0)!=esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.21/0.38  fof(c_0_19, plain, ![X18]:k2_tarski(X18,X18)=k1_tarski(X18), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.38  fof(c_0_20, plain, ![X19, X20]:k1_enumset1(X19,X19,X20)=k2_tarski(X19,X20), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.38  fof(c_0_21, plain, ![X21, X22, X23]:k2_enumset1(X21,X21,X22,X23)=k1_enumset1(X21,X22,X23), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.38  fof(c_0_22, plain, ![X9, X10, X11, X12, X13, X14, X15, X16]:(((~r2_hidden(X12,X11)|(X12=X9|X12=X10)|X11!=k2_tarski(X9,X10))&((X13!=X9|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))&(X13!=X10|r2_hidden(X13,X11)|X11!=k2_tarski(X9,X10))))&(((esk2_3(X14,X15,X16)!=X14|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15))&(esk2_3(X14,X15,X16)!=X15|~r2_hidden(esk2_3(X14,X15,X16),X16)|X16=k2_tarski(X14,X15)))&(r2_hidden(esk2_3(X14,X15,X16),X16)|(esk2_3(X14,X15,X16)=X14|esk2_3(X14,X15,X16)=X15)|X16=k2_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.38  cnf(c_0_23, plain, (m1_subset_1(k2_relset_1(X2,X3,X1),k1_zfmisc_1(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.38  cnf(c_0_24, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.38  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k1_tarski(esk7_0))))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.38  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.38  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.38  cnf(c_0_29, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  fof(c_0_30, plain, ![X26, X27, X28]:(~r2_hidden(X26,X27)|~m1_subset_1(X27,k1_zfmisc_1(X28))|m1_subset_1(X26,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.38  cnf(c_0_31, plain, (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.38  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.38  fof(c_0_33, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.38  cnf(c_0_34, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X4,X4,X4,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_27]), c_0_28])).
% 0.21/0.38  fof(c_0_35, plain, ![X45, X46, X47]:(~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))|k1_relset_1(X45,X46,X47)=k1_relat_1(X47)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.21/0.38  cnf(c_0_36, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.38  fof(c_0_37, plain, ![X24, X25]:(~m1_subset_1(X24,X25)|(v1_xboole_0(X25)|r2_hidden(X24,X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.21/0.38  cnf(c_0_38, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.38  cnf(c_0_39, negated_conjecture, (m1_subset_1(k2_relat_1(esk9_0),k1_zfmisc_1(k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.21/0.38  cnf(c_0_40, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.21/0.38  cnf(c_0_41, plain, (r2_hidden(X1,k2_enumset1(X2,X2,X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.21/0.38  fof(c_0_42, plain, ![X51, X52, X53]:((((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X52=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&((~v1_funct_2(X53,X51,X52)|X51=k1_relset_1(X51,X52,X53)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X51!=k1_relset_1(X51,X52,X53)|v1_funct_2(X53,X51,X52)|X51!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))))&((~v1_funct_2(X53,X51,X52)|X53=k1_xboole_0|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))))&(X53!=k1_xboole_0|v1_funct_2(X53,X51,X52)|X51=k1_xboole_0|X52!=k1_xboole_0|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.21/0.38  cnf(c_0_43, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.21/0.38  cnf(c_0_44, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,k1_tarski(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_45, plain, (X1=X4|X1=X3|X2!=k2_enumset1(X3,X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_27]), c_0_28])).
% 0.21/0.38  cnf(c_0_46, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.38  cnf(c_0_47, negated_conjecture, (m1_subset_1(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.21/0.38  cnf(c_0_48, plain, (~v1_xboole_0(k2_enumset1(X1,X1,X1,X2))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.21/0.38  fof(c_0_49, plain, ![X29, X30, X31, X33, X34, X35, X37]:((((r2_hidden(esk3_3(X29,X30,X31),k1_relat_1(X29))|~r2_hidden(X31,X30)|X30!=k2_relat_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X31=k1_funct_1(X29,esk3_3(X29,X30,X31))|~r2_hidden(X31,X30)|X30!=k2_relat_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&(~r2_hidden(X34,k1_relat_1(X29))|X33!=k1_funct_1(X29,X34)|r2_hidden(X33,X30)|X30!=k2_relat_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((~r2_hidden(esk4_2(X29,X35),X35)|(~r2_hidden(X37,k1_relat_1(X29))|esk4_2(X29,X35)!=k1_funct_1(X29,X37))|X35=k2_relat_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&((r2_hidden(esk5_2(X29,X35),k1_relat_1(X29))|r2_hidden(esk4_2(X29,X35),X35)|X35=k2_relat_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(esk4_2(X29,X35)=k1_funct_1(X29,esk5_2(X29,X35))|r2_hidden(esk4_2(X29,X35),X35)|X35=k2_relat_1(X29)|(~v1_relat_1(X29)|~v1_funct_1(X29)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.21/0.38  fof(c_0_50, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.21/0.38  cnf(c_0_51, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.38  cnf(c_0_52, negated_conjecture, (k1_relset_1(esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0),esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_43, c_0_32])).
% 0.21/0.38  cnf(c_0_53, negated_conjecture, (v1_funct_2(esk9_0,esk6_0,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_26]), c_0_27]), c_0_28])).
% 0.21/0.38  cnf(c_0_54, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_enumset1(X3,X3,X3,X2))), inference(er,[status(thm)],[c_0_45])).
% 0.21/0.38  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0))|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])).
% 0.21/0.38  cnf(c_0_56, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.38  cnf(c_0_57, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.38  cnf(c_0_58, negated_conjecture, (k2_enumset1(esk7_0,esk7_0,esk7_0,esk7_0)=k1_xboole_0|k1_relat_1(esk9_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_32]), c_0_52]), c_0_53])])).
% 0.21/0.38  cnf(c_0_59, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.21/0.38  cnf(c_0_60, negated_conjecture, (X1=esk7_0|~r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.21/0.38  cnf(c_0_61, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_56])])).
% 0.21/0.38  cnf(c_0_62, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_63, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_57, c_0_32])).
% 0.21/0.38  cnf(c_0_64, negated_conjecture, (k1_relat_1(esk9_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_58]), c_0_59])])).
% 0.21/0.38  cnf(c_0_65, negated_conjecture, (k1_funct_1(esk9_0,esk8_0)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_66, negated_conjecture, (k1_funct_1(esk9_0,X1)=esk7_0|~r2_hidden(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_63]), c_0_64])])).
% 0.21/0.38  cnf(c_0_67, negated_conjecture, (r2_hidden(esk8_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.38  cnf(c_0_68, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_67])]), ['proof']).
% 0.21/0.38  # SZS output end CNFRefutation
% 0.21/0.38  # Proof object total steps             : 69
% 0.21/0.38  # Proof object clause steps            : 39
% 0.21/0.38  # Proof object formula steps           : 30
% 0.21/0.38  # Proof object conjectures             : 20
% 0.21/0.38  # Proof object clause conjectures      : 17
% 0.21/0.38  # Proof object formula conjectures     : 3
% 0.21/0.38  # Proof object initial clauses used    : 20
% 0.21/0.38  # Proof object initial formulas used   : 15
% 0.21/0.38  # Proof object generating inferences   : 12
% 0.21/0.38  # Proof object simplifying inferences  : 27
% 0.21/0.38  # Training examples: 0 positive, 0 negative
% 0.21/0.38  # Parsed axioms                        : 15
% 0.21/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.38  # Initial clauses                      : 35
% 0.21/0.38  # Removed in clause preprocessing      : 3
% 0.21/0.38  # Initial clauses in saturation        : 32
% 0.21/0.38  # Processed clauses                    : 103
% 0.21/0.38  # ...of these trivial                  : 0
% 0.21/0.38  # ...subsumed                          : 8
% 0.21/0.38  # ...remaining for further processing  : 95
% 0.21/0.38  # Other redundant clauses eliminated   : 14
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 2
% 0.21/0.38  # Generated clauses                    : 74
% 0.21/0.38  # ...of the previous two non-trivial   : 69
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 64
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 14
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 51
% 0.21/0.38  #    Positive orientable unit clauses  : 13
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 4
% 0.21/0.38  #    Non-unit-clauses                  : 34
% 0.21/0.38  # Current number of unprocessed clauses: 25
% 0.21/0.38  # ...number of literals in the above   : 79
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 37
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 323
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 134
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 2
% 0.21/0.38  # Unit Clause-clause subsumption calls : 18
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 3
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 3709
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.032 s
% 0.21/0.38  # System time              : 0.007 s
% 0.21/0.38  # Total time               : 0.038 s
% 0.21/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
