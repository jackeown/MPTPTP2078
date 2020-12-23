%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:08:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 174 expanded)
%              Number of clauses        :   46 (  72 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  248 ( 623 expanded)
%              Number of equality atoms :   81 ( 158 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t190_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X2,X3)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
     => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
          & ! [X5] :
              ( m1_subset_1(X5,X2)
             => X1 != k1_funct_1(X4,X5) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

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

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(t12_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,X2) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(l1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

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

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X2,X3)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
       => ~ ( r2_hidden(X1,k2_relset_1(X2,X3,X4))
            & ! [X5] :
                ( m1_subset_1(X5,X2)
               => X1 != k1_funct_1(X4,X5) ) ) ) ),
    inference(assume_negation,[status(cth)],[t190_funct_2])).

fof(c_0_18,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | r2_hidden(X9,X6)
        | r2_hidden(X9,X7)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X6)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X8 != k2_xboole_0(X6,X7) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X11)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk1_3(X11,X12,X13),X12)
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_xboole_0(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | r2_hidden(esk1_3(X11,X12,X13),X11)
        | r2_hidden(esk1_3(X11,X12,X13),X12)
        | X13 = k2_xboole_0(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X45,X46,X47] :
      ( ( v4_relat_1(X47,X45)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( v5_relat_1(X47,X46)
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_20,negated_conjecture,(
    ! [X61] :
      ( v1_funct_1(esk8_0)
      & v1_funct_2(esk8_0,esk6_0,esk7_0)
      & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))
      & r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0))
      & ( ~ m1_subset_1(X61,esk6_0)
        | esk5_0 != k1_funct_1(esk8_0,X61) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).

fof(c_0_21,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X29)
      | ~ m1_subset_1(X30,k1_zfmisc_1(X29))
      | v1_relat_1(X30) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_22,plain,(
    ! [X33,X34] : v1_relat_1(k2_zfmisc_1(X33,X34)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X51,X52,X53] :
      ( ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))
      | k2_relset_1(X51,X52,X53) = k2_relat_1(X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_25,plain,(
    ! [X31,X32] :
      ( ( ~ v5_relat_1(X32,X31)
        | r1_tarski(k2_relat_1(X32),X31)
        | ~ v1_relat_1(X32) )
      & ( ~ r1_tarski(k2_relat_1(X32),X31)
        | v5_relat_1(X32,X31)
        | ~ v1_relat_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_26,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X15,X16] :
      ( ~ r1_tarski(X15,X16)
      | k2_xboole_0(X15,X16) = X16 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v5_relat_1(esk8_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_27]),c_0_29])])).

fof(c_0_37,plain,(
    ! [X23,X24] :
      ( ( ~ r1_tarski(k1_tarski(X23),X24)
        | r2_hidden(X23,X24) )
      & ( ~ r2_hidden(X23,X24)
        | r1_tarski(k1_tarski(X23),X24) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).

fof(c_0_38,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_39,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_40,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk5_0,k2_xboole_0(k2_relset_1(esk6_0,esk7_0,esk8_0),X1)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( k2_relset_1(esk6_0,esk7_0,esk8_0) = k2_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_27])).

cnf(c_0_43,plain,
    ( k2_xboole_0(X1,X2) = X2
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_45,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk5_0,k2_xboole_0(k2_relat_1(esk8_0),X1)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(esk8_0),esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

fof(c_0_51,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k1_relset_1(X48,X49,X50) = k1_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_52,plain,(
    ! [X25,X26] : k2_xboole_0(k1_tarski(X25),X26) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

fof(c_0_55,plain,(
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

cnf(c_0_56,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_57,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

fof(c_0_59,plain,(
    ! [X35,X36,X37,X39,X40,X41,X43] :
      ( ( r2_hidden(esk2_3(X35,X36,X37),k1_relat_1(X35))
        | ~ r2_hidden(X37,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( X37 = k1_funct_1(X35,esk2_3(X35,X36,X37))
        | ~ r2_hidden(X37,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(X40,k1_relat_1(X35))
        | X39 != k1_funct_1(X35,X40)
        | r2_hidden(X39,X36)
        | X36 != k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( ~ r2_hidden(esk3_2(X35,X41),X41)
        | ~ r2_hidden(X43,k1_relat_1(X35))
        | esk3_2(X35,X41) != k1_funct_1(X35,X43)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( r2_hidden(esk4_2(X35,X41),k1_relat_1(X35))
        | r2_hidden(esk3_2(X35,X41),X41)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( esk3_2(X35,X41) = k1_funct_1(X35,esk4_2(X35,X41))
        | r2_hidden(esk3_2(X35,X41),X41)
        | X41 = k2_relat_1(X35)
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_60,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk8_0,esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_62,negated_conjecture,
    ( k1_relset_1(esk6_0,esk7_0,esk8_0) = k1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_27])).

cnf(c_0_63,plain,
    ( k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57,c_0_46]),c_0_47]),c_0_48])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk7_0) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_58])).

cnf(c_0_65,plain,
    ( X1 = k1_funct_1(X2,esk2_3(X2,X3,X1))
    | ~ r2_hidden(X1,X3)
    | X3 != k2_relat_1(X2)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))
    | ~ r2_hidden(X3,X2)
    | X2 != k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0
    | esk7_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_27])])).

cnf(c_0_68,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

cnf(c_0_69,plain,
    ( k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2)) = X2
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk5_0,k2_relat_1(esk8_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_42])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_72,plain,(
    ! [X27,X28] :
      ( ~ r2_hidden(X27,X28)
      | m1_subset_1(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_73,plain,
    ( r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_66])).

cnf(c_0_74,negated_conjecture,
    ( k1_relat_1(esk8_0) = esk6_0 ),
    inference(sr,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_subset_1(X1,esk6_0)
    | esk5_0 != k1_funct_1(esk8_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_76,negated_conjecture,
    ( k1_funct_1(esk8_0,esk2_3(esk8_0,k2_relat_1(esk8_0),esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_36])])).

cnf(c_0_77,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk2_3(esk8_0,k2_relat_1(esk8_0),esk5_0),esk6_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_70]),c_0_71]),c_0_36])]),c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( ~ m1_subset_1(esk2_3(esk8_0,k2_relat_1(esk8_0),esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.20/0.37  # and selection function SelectCQArNTNpEqFirst.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.029 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(t190_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 0.20/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.37  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.20/0.37  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.20/0.37  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.20/0.37  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.20/0.37  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 0.20/0.37  fof(t12_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,X2)=X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 0.20/0.37  fof(l1_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 0.20/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.37  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.20/0.37  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.20/0.37  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.20/0.37  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.20/0.37  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.20/0.37  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 0.20/0.37  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.20/0.37  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X2,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))))=>~((r2_hidden(X1,k2_relset_1(X2,X3,X4))&![X5]:(m1_subset_1(X5,X2)=>X1!=k1_funct_1(X4,X5)))))), inference(assume_negation,[status(cth)],[t190_funct_2])).
% 0.20/0.37  fof(c_0_18, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(r2_hidden(X9,X6)|r2_hidden(X9,X7))|X8!=k2_xboole_0(X6,X7))&((~r2_hidden(X10,X6)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))&(~r2_hidden(X10,X7)|r2_hidden(X10,X8)|X8!=k2_xboole_0(X6,X7))))&(((~r2_hidden(esk1_3(X11,X12,X13),X11)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12))&(~r2_hidden(esk1_3(X11,X12,X13),X12)|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_xboole_0(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(r2_hidden(esk1_3(X11,X12,X13),X11)|r2_hidden(esk1_3(X11,X12,X13),X12))|X13=k2_xboole_0(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.37  fof(c_0_19, plain, ![X45, X46, X47]:((v4_relat_1(X47,X45)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(v5_relat_1(X47,X46)|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.20/0.37  fof(c_0_20, negated_conjecture, ![X61]:(((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,esk6_0,esk7_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0))))&(r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0))&(~m1_subset_1(X61,esk6_0)|esk5_0!=k1_funct_1(esk8_0,X61)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])])).
% 0.20/0.37  fof(c_0_21, plain, ![X29, X30]:(~v1_relat_1(X29)|(~m1_subset_1(X30,k1_zfmisc_1(X29))|v1_relat_1(X30))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.20/0.37  fof(c_0_22, plain, ![X33, X34]:v1_relat_1(k2_zfmisc_1(X33,X34)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.20/0.37  cnf(c_0_23, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.37  fof(c_0_24, plain, ![X51, X52, X53]:(~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))|k2_relset_1(X51,X52,X53)=k2_relat_1(X53)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.20/0.37  fof(c_0_25, plain, ![X31, X32]:((~v5_relat_1(X32,X31)|r1_tarski(k2_relat_1(X32),X31)|~v1_relat_1(X32))&(~r1_tarski(k2_relat_1(X32),X31)|v5_relat_1(X32,X31)|~v1_relat_1(X32))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 0.20/0.37  cnf(c_0_26, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.37  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(esk6_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_28, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_29, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.37  cnf(c_0_30, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_23])).
% 0.20/0.37  cnf(c_0_31, negated_conjecture, (r2_hidden(esk5_0,k2_relset_1(esk6_0,esk7_0,esk8_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_32, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.37  fof(c_0_33, plain, ![X15, X16]:(~r1_tarski(X15,X16)|k2_xboole_0(X15,X16)=X16), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_xboole_1])])).
% 0.20/0.37  cnf(c_0_34, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.37  cnf(c_0_35, negated_conjecture, (v5_relat_1(esk8_0,esk7_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.37  cnf(c_0_36, negated_conjecture, (v1_relat_1(esk8_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_27]), c_0_29])])).
% 0.20/0.37  fof(c_0_37, plain, ![X23, X24]:((~r1_tarski(k1_tarski(X23),X24)|r2_hidden(X23,X24))&(~r2_hidden(X23,X24)|r1_tarski(k1_tarski(X23),X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l1_zfmisc_1])])).
% 0.20/0.37  fof(c_0_38, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.37  fof(c_0_39, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.20/0.37  fof(c_0_40, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.20/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk5_0,k2_xboole_0(k2_relset_1(esk6_0,esk7_0,esk8_0),X1))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.37  cnf(c_0_42, negated_conjecture, (k2_relset_1(esk6_0,esk7_0,esk8_0)=k2_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_32, c_0_27])).
% 0.20/0.37  cnf(c_0_43, plain, (k2_xboole_0(X1,X2)=X2|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.37  cnf(c_0_44, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])])).
% 0.20/0.37  cnf(c_0_45, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.37  cnf(c_0_46, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.37  cnf(c_0_47, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.37  cnf(c_0_48, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, (r2_hidden(esk5_0,k2_xboole_0(k2_relat_1(esk8_0),X1))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.37  cnf(c_0_50, negated_conjecture, (k2_xboole_0(k2_relat_1(esk8_0),esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.20/0.37  fof(c_0_51, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k1_relset_1(X48,X49,X50)=k1_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.20/0.37  fof(c_0_52, plain, ![X25, X26]:k2_xboole_0(k1_tarski(X25),X26)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.20/0.37  cnf(c_0_53, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X1),X2)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_48])).
% 0.20/0.37  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,esk7_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.20/0.37  fof(c_0_55, plain, ![X54, X55, X56]:((((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X55=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))&((~v1_funct_2(X56,X54,X55)|X54=k1_relset_1(X54,X55,X56)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X54!=k1_relset_1(X54,X55,X56)|v1_funct_2(X56,X54,X55)|X54!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))))&((~v1_funct_2(X56,X54,X55)|X56=k1_xboole_0|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55))))&(X56!=k1_xboole_0|v1_funct_2(X56,X54,X55)|X54=k1_xboole_0|X55!=k1_xboole_0|~m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.20/0.37  cnf(c_0_56, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.37  cnf(c_0_57, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.20/0.37  cnf(c_0_58, negated_conjecture, (r1_tarski(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.37  fof(c_0_59, plain, ![X35, X36, X37, X39, X40, X41, X43]:((((r2_hidden(esk2_3(X35,X36,X37),k1_relat_1(X35))|~r2_hidden(X37,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(X37=k1_funct_1(X35,esk2_3(X35,X36,X37))|~r2_hidden(X37,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&(~r2_hidden(X40,k1_relat_1(X35))|X39!=k1_funct_1(X35,X40)|r2_hidden(X39,X36)|X36!=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35))))&((~r2_hidden(esk3_2(X35,X41),X41)|(~r2_hidden(X43,k1_relat_1(X35))|esk3_2(X35,X41)!=k1_funct_1(X35,X43))|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&((r2_hidden(esk4_2(X35,X41),k1_relat_1(X35))|r2_hidden(esk3_2(X35,X41),X41)|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(esk3_2(X35,X41)=k1_funct_1(X35,esk4_2(X35,X41))|r2_hidden(esk3_2(X35,X41),X41)|X41=k2_relat_1(X35)|(~v1_relat_1(X35)|~v1_funct_1(X35)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.20/0.37  cnf(c_0_60, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.20/0.37  cnf(c_0_61, negated_conjecture, (v1_funct_2(esk8_0,esk6_0,esk7_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_62, negated_conjecture, (k1_relset_1(esk6_0,esk7_0,esk8_0)=k1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_56, c_0_27])).
% 0.20/0.37  cnf(c_0_63, plain, (k2_xboole_0(k2_enumset1(X1,X1,X1,X1),X2)!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_57, c_0_46]), c_0_47]), c_0_48])).
% 0.20/0.37  cnf(c_0_64, negated_conjecture, (k2_xboole_0(k2_enumset1(esk5_0,esk5_0,esk5_0,esk5_0),esk7_0)=esk7_0), inference(spm,[status(thm)],[c_0_43, c_0_58])).
% 0.20/0.37  cnf(c_0_65, plain, (X1=k1_funct_1(X2,esk2_3(X2,X3,X1))|~r2_hidden(X1,X3)|X3!=k2_relat_1(X2)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.37  cnf(c_0_66, plain, (r2_hidden(esk2_3(X1,X2,X3),k1_relat_1(X1))|~r2_hidden(X3,X2)|X2!=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 0.20/0.37  cnf(c_0_67, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0|esk7_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62]), c_0_27])])).
% 0.20/0.37  cnf(c_0_68, negated_conjecture, (esk7_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_63, c_0_64])).
% 0.20/0.37  cnf(c_0_69, plain, (k1_funct_1(X1,esk2_3(X1,k2_relat_1(X1),X2))=X2|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_65])).
% 0.20/0.37  cnf(c_0_70, negated_conjecture, (r2_hidden(esk5_0,k2_relat_1(esk8_0))), inference(rw,[status(thm)],[c_0_31, c_0_42])).
% 0.20/0.37  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  fof(c_0_72, plain, ![X27, X28]:(~r2_hidden(X27,X28)|m1_subset_1(X27,X28)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.20/0.37  cnf(c_0_73, plain, (r2_hidden(esk2_3(X1,k2_relat_1(X1),X2),k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_66])).
% 0.20/0.37  cnf(c_0_74, negated_conjecture, (k1_relat_1(esk8_0)=esk6_0), inference(sr,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.37  cnf(c_0_75, negated_conjecture, (~m1_subset_1(X1,esk6_0)|esk5_0!=k1_funct_1(esk8_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_76, negated_conjecture, (k1_funct_1(esk8_0,esk2_3(esk8_0,k2_relat_1(esk8_0),esk5_0))=esk5_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_36])])).
% 0.20/0.37  cnf(c_0_77, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.37  cnf(c_0_78, negated_conjecture, (r2_hidden(esk2_3(esk8_0,k2_relat_1(esk8_0),esk5_0),esk6_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_70]), c_0_71]), c_0_36])]), c_0_74])).
% 0.20/0.37  cnf(c_0_79, negated_conjecture, (~m1_subset_1(esk2_3(esk8_0,k2_relat_1(esk8_0),esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_75, c_0_76])).
% 0.20/0.37  cnf(c_0_80, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 81
% 0.20/0.37  # Proof object clause steps            : 46
% 0.20/0.37  # Proof object formula steps           : 35
% 0.20/0.37  # Proof object conjectures             : 27
% 0.20/0.37  # Proof object clause conjectures      : 24
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 22
% 0.20/0.37  # Proof object initial formulas used   : 17
% 0.20/0.37  # Proof object generating inferences   : 16
% 0.20/0.37  # Proof object simplifying inferences  : 27
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 17
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 39
% 0.20/0.37  # Removed in clause preprocessing      : 3
% 0.20/0.37  # Initial clauses in saturation        : 36
% 0.20/0.37  # Processed clauses                    : 117
% 0.20/0.37  # ...of these trivial                  : 2
% 0.20/0.37  # ...subsumed                          : 0
% 0.20/0.37  # ...remaining for further processing  : 115
% 0.20/0.37  # Other redundant clauses eliminated   : 12
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 5
% 0.20/0.37  # Generated clauses                    : 120
% 0.20/0.37  # ...of the previous two non-trivial   : 101
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 103
% 0.20/0.37  # Factorizations                       : 6
% 0.20/0.37  # Equation resolutions                 : 12
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 63
% 0.20/0.37  #    Positive orientable unit clauses  : 29
% 0.20/0.37  #    Positive unorientable unit clauses: 0
% 0.20/0.37  #    Negative unit clauses             : 3
% 0.20/0.37  #    Non-unit-clauses                  : 31
% 0.20/0.37  # Current number of unprocessed clauses: 50
% 0.20/0.37  # ...number of literals in the above   : 173
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 45
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 756
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 329
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 0
% 0.20/0.37  # Unit Clause-clause subsumption calls : 17
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 2
% 0.20/0.37  # BW rewrite match successes           : 2
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 4525
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.032 s
% 0.20/0.37  # System time              : 0.007 s
% 0.20/0.37  # Total time               : 0.039 s
% 0.20/0.37  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
