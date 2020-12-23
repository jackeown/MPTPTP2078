%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:47 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 630 expanded)
%              Number of clauses        :   57 ( 266 expanded)
%              Number of leaves         :   19 ( 173 expanded)
%              Depth                    :   14
%              Number of atoms          :  255 (1392 expanded)
%              Number of equality atoms :   64 ( 358 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

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

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t14_funct_1,axiom,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( k1_relat_1(X2) = k1_tarski(X1)
       => k2_relat_1(X2) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk5_0),esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))
    & esk6_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_23,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_24,plain,(
    ! [X65,X66,X67,X68] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | k7_relset_1(X65,X66,X67,X68) = k9_relat_1(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X30))
      | v1_relat_1(X31) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_30,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

fof(c_0_34,plain,(
    ! [X55,X56] :
      ( ~ v1_relat_1(X56)
      | ~ v1_funct_1(X56)
      | k1_relat_1(X56) != k1_tarski(X55)
      | k2_relat_1(X56) = k1_tarski(k1_funct_1(X56,X55)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).

fof(c_0_35,plain,(
    ! [X36,X37] : v1_relat_1(k2_zfmisc_1(X36,X37)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_36,plain,(
    ! [X62,X63,X64] :
      ( ( v4_relat_1(X64,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v5_relat_1(X64,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_37,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,esk7_0),k2_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k7_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,X1) = k9_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X1) != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X45,X46,X47,X49,X50,X51,X53] :
      ( ( r2_hidden(esk2_3(X45,X46,X47),k1_relat_1(X45))
        | ~ r2_hidden(X47,X46)
        | X46 != k2_relat_1(X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( X47 = k1_funct_1(X45,esk2_3(X45,X46,X47))
        | ~ r2_hidden(X47,X46)
        | X46 != k2_relat_1(X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( ~ r2_hidden(X50,k1_relat_1(X45))
        | X49 != k1_funct_1(X45,X50)
        | r2_hidden(X49,X46)
        | X46 != k2_relat_1(X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( ~ r2_hidden(esk3_2(X45,X51),X51)
        | ~ r2_hidden(X53,k1_relat_1(X45))
        | esk3_2(X45,X51) != k1_funct_1(X45,X53)
        | X51 = k2_relat_1(X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( r2_hidden(esk4_2(X45,X51),k1_relat_1(X45))
        | r2_hidden(esk3_2(X45,X51),X51)
        | X51 = k2_relat_1(X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) )
      & ( esk3_2(X45,X51) = k1_funct_1(X45,esk4_2(X45,X51))
        | r2_hidden(esk3_2(X45,X51),X51)
        | X51 = k2_relat_1(X45)
        | ~ v1_relat_1(X45)
        | ~ v1_funct_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

fof(c_0_44,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_45,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_46,plain,(
    ! [X34,X35] :
      ( ( ~ v5_relat_1(X35,X34)
        | r1_tarski(k2_relat_1(X35),X34)
        | ~ v1_relat_1(X35) )
      & ( ~ r1_tarski(k2_relat_1(X35),X34)
        | v5_relat_1(X35,X34)
        | ~ v1_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_47,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_49,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X43)
      | ~ v1_funct_1(X43)
      | ~ m1_subset_1(X44,k1_zfmisc_1(X43))
      | v1_funct_1(X44) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

fof(c_0_50,plain,(
    ! [X32,X33] :
      ( ( ~ v4_relat_1(X33,X32)
        | r1_tarski(k1_relat_1(X33),X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r1_tarski(k1_relat_1(X33),X32)
        | v4_relat_1(X33,X32)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_51,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_52,plain,(
    ! [X20,X21] :
      ( ( ~ r1_tarski(X20,k1_tarski(X21))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X21) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k1_tarski(X21)) )
      & ( X20 != k1_tarski(X21)
        | r1_tarski(X20,k1_tarski(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk8_0,esk7_0),k2_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_54,plain,
    ( k2_relat_1(X1) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))
    | k1_relat_1(X1) != k2_enumset1(X2,X2,X2,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_55,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_56,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_33]),c_0_42])])).

fof(c_0_57,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k9_relat_1(X39,X38),k2_relat_1(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

fof(c_0_58,plain,(
    ! [X57,X58] :
      ( ~ r2_hidden(X57,X58)
      | ~ r1_tarski(X58,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_59,plain,
    ( r2_hidden(X3,X4)
    | ~ r2_hidden(X1,k1_relat_1(X2))
    | X3 != k1_funct_1(X2,X1)
    | X4 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_61,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_62,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_63,plain,
    ( v5_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_38])).

cnf(c_0_64,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_42])).

cnf(c_0_65,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_67,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_38])).

cnf(c_0_68,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( v4_relat_1(esk8_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) != k1_relat_1(esk8_0)
    | ~ r1_tarski(k9_relat_1(esk8_0,esk7_0),k2_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_56])])).

cnf(c_0_71,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_73,plain,
    ( r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_59])])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_75,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])])).

cnf(c_0_76,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_38])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_64])])).

cnf(c_0_78,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68,c_0_26]),c_0_26]),c_0_27]),c_0_27]),c_0_28]),c_0_28])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_69]),c_0_56])])).

cnf(c_0_81,negated_conjecture,
    ( k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0) != k1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_56])])).

cnf(c_0_82,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),k1_funct_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_83,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_55]),c_0_56])])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_74,c_0_77])).

cnf(c_0_86,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_87,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_88,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84]),c_0_64]),c_0_85]),c_0_61])])).

cnf(c_0_89,plain,
    ( r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk3_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_90,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_55]),c_0_56])]),c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_84]),c_0_83]),c_0_85]),c_0_64])]),c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( k2_relat_1(esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk8_0,X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_92]),c_0_56])])).

cnf(c_0_94,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_93]),c_0_61])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_94]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.40  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.14/0.40  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.40  #
% 0.14/0.40  # Preprocessing time       : 0.029 s
% 0.14/0.40  
% 0.14/0.40  # Proof found!
% 0.14/0.40  # SZS status Theorem
% 0.14/0.40  # SZS output start CNFRefutation
% 0.14/0.40  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.14/0.40  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.14/0.40  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.14/0.40  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.14/0.40  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.14/0.40  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.14/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.14/0.40  fof(t14_funct_1, axiom, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(k1_relat_1(X2)=k1_tarski(X1)=>k2_relat_1(X2)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 0.14/0.40  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.14/0.40  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.14/0.40  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.14/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.14/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.14/0.40  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.14/0.40  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 0.14/0.40  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.14/0.40  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.14/0.40  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.14/0.40  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.14/0.40  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.14/0.40  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk5_0),esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))))&(esk6_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 0.14/0.40  fof(c_0_21, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.14/0.40  fof(c_0_22, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.14/0.40  fof(c_0_23, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.14/0.40  fof(c_0_24, plain, ![X65, X66, X67, X68]:(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|k7_relset_1(X65,X66,X67,X68)=k9_relat_1(X67,X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.14/0.40  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.40  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.14/0.40  fof(c_0_29, plain, ![X30, X31]:(~v1_relat_1(X30)|(~m1_subset_1(X31,k1_zfmisc_1(X30))|v1_relat_1(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.14/0.40  fof(c_0_30, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.14/0.40  cnf(c_0_31, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_32, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.40  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.40  fof(c_0_34, plain, ![X55, X56]:(~v1_relat_1(X56)|~v1_funct_1(X56)|(k1_relat_1(X56)!=k1_tarski(X55)|k2_relat_1(X56)=k1_tarski(k1_funct_1(X56,X55)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_funct_1])])).
% 0.14/0.40  fof(c_0_35, plain, ![X36, X37]:v1_relat_1(k2_zfmisc_1(X36,X37)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.14/0.40  fof(c_0_36, plain, ![X62, X63, X64]:((v4_relat_1(X64,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(v5_relat_1(X64,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.14/0.40  cnf(c_0_37, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.14/0.40  cnf(c_0_38, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.14/0.40  cnf(c_0_39, negated_conjecture, (~r1_tarski(k7_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,esk7_0),k2_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.14/0.40  cnf(c_0_40, negated_conjecture, (k7_relset_1(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,X1)=k9_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.14/0.40  cnf(c_0_41, plain, (k2_relat_1(X1)=k1_tarski(k1_funct_1(X1,X2))|~v1_relat_1(X1)|~v1_funct_1(X1)|k1_relat_1(X1)!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.14/0.40  cnf(c_0_42, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.14/0.40  fof(c_0_43, plain, ![X45, X46, X47, X49, X50, X51, X53]:((((r2_hidden(esk2_3(X45,X46,X47),k1_relat_1(X45))|~r2_hidden(X47,X46)|X46!=k2_relat_1(X45)|(~v1_relat_1(X45)|~v1_funct_1(X45)))&(X47=k1_funct_1(X45,esk2_3(X45,X46,X47))|~r2_hidden(X47,X46)|X46!=k2_relat_1(X45)|(~v1_relat_1(X45)|~v1_funct_1(X45))))&(~r2_hidden(X50,k1_relat_1(X45))|X49!=k1_funct_1(X45,X50)|r2_hidden(X49,X46)|X46!=k2_relat_1(X45)|(~v1_relat_1(X45)|~v1_funct_1(X45))))&((~r2_hidden(esk3_2(X45,X51),X51)|(~r2_hidden(X53,k1_relat_1(X45))|esk3_2(X45,X51)!=k1_funct_1(X45,X53))|X51=k2_relat_1(X45)|(~v1_relat_1(X45)|~v1_funct_1(X45)))&((r2_hidden(esk4_2(X45,X51),k1_relat_1(X45))|r2_hidden(esk3_2(X45,X51),X51)|X51=k2_relat_1(X45)|(~v1_relat_1(X45)|~v1_funct_1(X45)))&(esk3_2(X45,X51)=k1_funct_1(X45,esk4_2(X45,X51))|r2_hidden(esk3_2(X45,X51),X51)|X51=k2_relat_1(X45)|(~v1_relat_1(X45)|~v1_funct_1(X45)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.14/0.40  fof(c_0_44, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.14/0.40  fof(c_0_45, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.14/0.40  fof(c_0_46, plain, ![X34, X35]:((~v5_relat_1(X35,X34)|r1_tarski(k2_relat_1(X35),X34)|~v1_relat_1(X35))&(~r1_tarski(k2_relat_1(X35),X34)|v5_relat_1(X35,X34)|~v1_relat_1(X35))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.14/0.40  cnf(c_0_47, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  cnf(c_0_48, plain, (v1_relat_1(k1_xboole_0)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.14/0.40  fof(c_0_49, plain, ![X43, X44]:(~v1_relat_1(X43)|~v1_funct_1(X43)|(~m1_subset_1(X44,k1_zfmisc_1(X43))|v1_funct_1(X44))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 0.14/0.40  fof(c_0_50, plain, ![X32, X33]:((~v4_relat_1(X33,X32)|r1_tarski(k1_relat_1(X33),X32)|~v1_relat_1(X33))&(~r1_tarski(k1_relat_1(X33),X32)|v4_relat_1(X33,X32)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.14/0.40  cnf(c_0_51, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.14/0.40  fof(c_0_52, plain, ![X20, X21]:((~r1_tarski(X20,k1_tarski(X21))|(X20=k1_xboole_0|X20=k1_tarski(X21)))&((X20!=k1_xboole_0|r1_tarski(X20,k1_tarski(X21)))&(X20!=k1_tarski(X21)|r1_tarski(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.14/0.40  cnf(c_0_53, negated_conjecture, (~r1_tarski(k9_relat_1(esk8_0,esk7_0),k2_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0)))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.14/0.40  cnf(c_0_54, plain, (k2_relat_1(X1)=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2))|k1_relat_1(X1)!=k2_enumset1(X2,X2,X2,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.14/0.40  cnf(c_0_55, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_56, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_33]), c_0_42])])).
% 0.14/0.40  fof(c_0_57, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k9_relat_1(X39,X38),k2_relat_1(X39))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.14/0.40  fof(c_0_58, plain, ![X57, X58]:(~r2_hidden(X57,X58)|~r1_tarski(X58,X57)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.14/0.40  cnf(c_0_59, plain, (r2_hidden(X3,X4)|~r2_hidden(X1,k1_relat_1(X2))|X3!=k1_funct_1(X2,X1)|X4!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.40  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.14/0.40  cnf(c_0_61, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.14/0.40  cnf(c_0_62, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.14/0.40  cnf(c_0_63, plain, (v5_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_47, c_0_38])).
% 0.14/0.40  cnf(c_0_64, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_48, c_0_42])).
% 0.14/0.40  cnf(c_0_65, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.14/0.40  cnf(c_0_66, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.14/0.40  cnf(c_0_67, plain, (v4_relat_1(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_51, c_0_38])).
% 0.14/0.40  cnf(c_0_68, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.14/0.40  cnf(c_0_69, negated_conjecture, (v4_relat_1(esk8_0,k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_33])).
% 0.14/0.40  cnf(c_0_70, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)!=k1_relat_1(esk8_0)|~r1_tarski(k9_relat_1(esk8_0,esk7_0),k2_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55]), c_0_56])])).
% 0.14/0.40  cnf(c_0_71, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.14/0.40  cnf(c_0_72, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.14/0.40  cnf(c_0_73, plain, (r2_hidden(k1_funct_1(X1,X2),k2_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_59])])).
% 0.14/0.40  cnf(c_0_74, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.14/0.40  cnf(c_0_75, plain, (r1_tarski(k2_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_64])])).
% 0.14/0.40  cnf(c_0_76, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_65, c_0_38])).
% 0.14/0.40  cnf(c_0_77, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_64])])).
% 0.14/0.40  cnf(c_0_78, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.40  cnf(c_0_79, plain, (X1=k1_xboole_0|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_68, c_0_26]), c_0_26]), c_0_27]), c_0_27]), c_0_28]), c_0_28])).
% 0.14/0.40  cnf(c_0_80, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_69]), c_0_56])])).
% 0.14/0.40  cnf(c_0_81, negated_conjecture, (k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0)!=k1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_56])])).
% 0.14/0.40  cnf(c_0_82, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r1_tarski(k2_relat_1(X1),k1_funct_1(X1,X2))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 0.14/0.40  cnf(c_0_83, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.14/0.40  cnf(c_0_84, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_55]), c_0_56])])).
% 0.14/0.40  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_74, c_0_77])).
% 0.14/0.40  cnf(c_0_86, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_78])).
% 0.14/0.40  cnf(c_0_87, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.14/0.40  cnf(c_0_88, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84]), c_0_64]), c_0_85]), c_0_61])])).
% 0.14/0.40  cnf(c_0_89, plain, (r2_hidden(esk4_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk3_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.40  cnf(c_0_90, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk8_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_55]), c_0_56])]), c_0_88])).
% 0.14/0.40  cnf(c_0_91, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_84]), c_0_83]), c_0_85]), c_0_64])]), c_0_88])).
% 0.14/0.40  cnf(c_0_92, negated_conjecture, (k2_relat_1(esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_90, c_0_91])).
% 0.14/0.40  cnf(c_0_93, negated_conjecture, (r1_tarski(k9_relat_1(esk8_0,X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_92]), c_0_56])])).
% 0.14/0.40  cnf(c_0_94, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_93]), c_0_61])])).
% 0.14/0.40  cnf(c_0_95, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_94]), c_0_61])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 96
% 0.14/0.40  # Proof object clause steps            : 57
% 0.14/0.40  # Proof object formula steps           : 39
% 0.14/0.40  # Proof object conjectures             : 23
% 0.14/0.40  # Proof object clause conjectures      : 20
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 24
% 0.14/0.40  # Proof object initial formulas used   : 19
% 0.14/0.40  # Proof object generating inferences   : 25
% 0.14/0.40  # Proof object simplifying inferences  : 62
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 26
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 47
% 0.14/0.40  # Removed in clause preprocessing      : 3
% 0.14/0.40  # Initial clauses in saturation        : 44
% 0.14/0.40  # Processed clauses                    : 285
% 0.14/0.40  # ...of these trivial                  : 2
% 0.14/0.40  # ...subsumed                          : 82
% 0.14/0.40  # ...remaining for further processing  : 201
% 0.14/0.40  # Other redundant clauses eliminated   : 10
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 7
% 0.14/0.40  # Backward-rewritten                   : 30
% 0.14/0.40  # Generated clauses                    : 801
% 0.14/0.40  # ...of the previous two non-trivial   : 438
% 0.14/0.40  # Contextual simplify-reflections      : 5
% 0.14/0.40  # Paramodulations                      : 792
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 10
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 155
% 0.14/0.40  #    Positive orientable unit clauses  : 64
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 6
% 0.14/0.40  #    Non-unit-clauses                  : 85
% 0.14/0.40  # Current number of unprocessed clauses: 183
% 0.14/0.40  # ...number of literals in the above   : 484
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 40
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 1578
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 981
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 66
% 0.14/0.40  # Unit Clause-clause subsumption calls : 146
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 41
% 0.14/0.40  # BW rewrite match successes           : 10
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 12970
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.046 s
% 0.14/0.40  # System time              : 0.004 s
% 0.14/0.40  # Total time               : 0.050 s
% 0.14/0.40  # Maximum resident set size: 1604 pages
%------------------------------------------------------------------------------
