%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:04 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 832 expanded)
%              Number of clauses        :   50 ( 330 expanded)
%              Number of leaves         :   17 ( 238 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 (1640 expanded)
%              Number of equality atoms :  113 ( 803 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   25 (   2 average)
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

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t142_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(X4,k1_enumset1(X1,X2,X3))
    <=> ~ ( X4 != k1_xboole_0
          & X4 != k1_tarski(X1)
          & X4 != k1_tarski(X2)
          & X4 != k1_tarski(X3)
          & X4 != k2_tarski(X1,X2)
          & X4 != k2_tarski(X2,X3)
          & X4 != k2_tarski(X1,X3)
          & X4 != k1_enumset1(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t65_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( k1_relat_1(X1) = k1_xboole_0
      <=> k2_relat_1(X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(t118_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k1_relat_1(X3)) )
       => k9_relat_1(X3,k2_tarski(X1,X2)) = k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))
    & esk3_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_19,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_20,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_22,plain,(
    ! [X40,X41,X42] :
      ( ( v4_relat_1(X42,X40)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) )
      & ( v5_relat_1(X42,X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_27,plain,(
    ! [X27,X28] :
      ( ~ v1_relat_1(X27)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X27))
      | v1_relat_1(X28) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_28,plain,(
    ! [X31,X32] : v1_relat_1(k2_zfmisc_1(X31,X32)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_29,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X11,X10)
        | X11 = X8
        | X11 = X9
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X8
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( X12 != X9
        | r2_hidden(X12,X10)
        | X10 != k2_tarski(X8,X9) )
      & ( esk1_3(X13,X14,X15) != X13
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( esk1_3(X13,X14,X15) != X14
        | ~ r2_hidden(esk1_3(X13,X14,X15),X15)
        | X15 = k2_tarski(X13,X14) )
      & ( r2_hidden(esk1_3(X13,X14,X15),X15)
        | esk1_3(X13,X14,X15) = X13
        | esk1_3(X13,X14,X15) = X14
        | X15 = k2_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ r1_tarski(X26,k1_enumset1(X23,X24,X25))
        | X26 = k1_xboole_0
        | X26 = k1_tarski(X23)
        | X26 = k1_tarski(X24)
        | X26 = k1_tarski(X25)
        | X26 = k2_tarski(X23,X24)
        | X26 = k2_tarski(X24,X25)
        | X26 = k2_tarski(X23,X25)
        | X26 = k1_enumset1(X23,X24,X25) )
      & ( X26 != k1_xboole_0
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k1_tarski(X23)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k1_tarski(X24)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k1_tarski(X25)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k2_tarski(X23,X24)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k2_tarski(X24,X25)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k2_tarski(X23,X25)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) )
      & ( X26 != k1_enumset1(X23,X24,X25)
        | r1_tarski(X26,k1_enumset1(X23,X24,X25)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).

fof(c_0_31,plain,(
    ! [X29,X30] :
      ( ( ~ v4_relat_1(X30,X29)
        | r1_tarski(k1_relat_1(X30),X29)
        | ~ v1_relat_1(X30) )
      & ( ~ r1_tarski(k1_relat_1(X30),X29)
        | v4_relat_1(X30,X29)
        | ~ v1_relat_1(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_32,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])).

cnf(c_0_34,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | X1 = k1_tarski(X3)
    | X1 = k1_tarski(X4)
    | X1 = k2_tarski(X2,X3)
    | X1 = k2_tarski(X3,X4)
    | X1 = k2_tarski(X2,X4)
    | X1 = k1_enumset1(X2,X3,X4)
    | ~ r1_tarski(X1,k1_enumset1(X2,X3,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k1_enumset1(X2,X3,X4))
    | X1 != k2_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_42,plain,(
    ! [X33,X34] :
      ( ~ v1_relat_1(X34)
      | r1_tarski(k9_relat_1(X34,X33),k2_relat_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_enumset1(X2,X2,X2,X4) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_25]),c_0_26])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | X1 = k2_enumset1(X4,X4,X4,X4)
    | X1 = k2_enumset1(X3,X3,X3,X4)
    | X1 = k2_enumset1(X3,X3,X3,X3)
    | X1 = k2_enumset1(X2,X2,X3,X4)
    | X1 = k2_enumset1(X2,X2,X2,X4)
    | X1 = k2_enumset1(X2,X2,X2,X3)
    | X1 = k2_enumset1(X2,X2,X2,X2)
    | ~ r1_tarski(X1,k2_enumset1(X2,X2,X3,X4)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_24]),c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_25]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26]),c_0_26])).

cnf(c_0_45,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))
    | X1 != k2_enumset1(X2,X2,X2,X3) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_25]),c_0_26]),c_0_26])).

fof(c_0_47,plain,(
    ! [X43,X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k7_relset_1(X43,X44,X45,X46) = k9_relat_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

fof(c_0_48,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_49,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_50,plain,(
    ! [X36] :
      ( ( k1_relat_1(X36) != k1_xboole_0
        | k2_relat_1(X36) = k1_xboole_0
        | ~ v1_relat_1(X36) )
      & ( k2_relat_1(X36) != k1_xboole_0
        | k1_relat_1(X36) = k1_xboole_0
        | ~ v1_relat_1(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k2_enumset1(X1,X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).

cnf(c_0_52,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_relat_1(esk5_0)
    | k1_relat_1(esk5_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_53,plain,
    ( r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X2,X3)) ),
    inference(er,[status(thm)],[c_0_46])).

fof(c_0_54,plain,(
    ! [X37,X38,X39] :
      ( ~ v1_relat_1(X39)
      | ~ v1_funct_1(X39)
      | ~ r2_hidden(X37,k1_relat_1(X39))
      | ~ r2_hidden(X38,k1_relat_1(X39))
      | k9_relat_1(X39,k2_tarski(X37,X38)) = k2_tarski(k1_funct_1(X39,X37),k1_funct_1(X39,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(k9_relat_1(esk5_0,X1),k2_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40])).

cnf(c_0_59,plain,
    ( k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_60,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

fof(c_0_61,plain,(
    ! [X7] : r1_tarski(k1_xboole_0,X7) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_62,negated_conjecture,
    ( k1_relat_1(esk5_0) = k1_xboole_0
    | r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

cnf(c_0_63,plain,
    ( k9_relat_1(X1,k2_tarski(X2,X3)) = k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_24]),c_0_24]),c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_65,negated_conjecture,
    ( k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1) = k9_relat_1(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_33])).

cnf(c_0_66,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) = k2_relat_1(esk5_0)
    | ~ r1_tarski(k2_relat_1(esk5_0),k9_relat_1(esk5_0,X1)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_67,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_40])])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( k2_relat_1(esk5_0) = k1_xboole_0
    | r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_62]),c_0_40])])).

cnf(c_0_70,plain,
    ( k9_relat_1(X1,k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_25]),c_0_25]),c_0_26]),c_0_26])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_72,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))) ),
    inference(rw,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) = k1_xboole_0
    | r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])])).

cnf(c_0_74,negated_conjecture,
    ( k9_relat_1(esk5_0,X1) = k1_xboole_0
    | r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_69]),c_0_68])])).

fof(c_0_75,plain,(
    ! [X35] :
      ( ~ v1_relat_1(X35)
      | k9_relat_1(X35,k1_relat_1(X35)) = k2_relat_1(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_76,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X2)) = k9_relat_1(esk5_0,k2_enumset1(X1,X1,X1,X2))
    | ~ r2_hidden(X2,k1_relat_1(esk5_0))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_40])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk2_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_68])])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_74]),c_0_68])])).

cnf(c_0_79,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,X1)) = k9_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_81,negated_conjecture,
    ( k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0) = k1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_78]),c_0_45])])).

cnf(c_0_82,negated_conjecture,
    ( k9_relat_1(esk5_0,k1_relat_1(esk5_0)) = k2_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_79,c_0_40])).

cnf(c_0_83,negated_conjecture,
    ( k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)) = k2_relat_1(esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_77]),c_0_81]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_83]),c_0_58])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.42  # AutoSched0-Mode selected heuristic G_E___208_C12_02_nc_F1_SE_CS_SP_PS_S002A
% 0.21/0.42  # and selection function SelectNegativeLiterals.
% 0.21/0.42  #
% 0.21/0.42  # Preprocessing time       : 0.028 s
% 0.21/0.42  # Presaturation interreduction done
% 0.21/0.42  
% 0.21/0.42  # Proof found!
% 0.21/0.42  # SZS status Theorem
% 0.21/0.42  # SZS output start CNFRefutation
% 0.21/0.42  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 0.21/0.42  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.21/0.42  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.21/0.42  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.21/0.42  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.21/0.42  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.21/0.42  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.21/0.42  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.21/0.42  fof(t142_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r1_tarski(X4,k1_enumset1(X1,X2,X3))<=>~((((((((X4!=k1_xboole_0&X4!=k1_tarski(X1))&X4!=k1_tarski(X2))&X4!=k1_tarski(X3))&X4!=k2_tarski(X1,X2))&X4!=k2_tarski(X2,X3))&X4!=k2_tarski(X1,X3))&X4!=k1_enumset1(X1,X2,X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 0.21/0.42  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.21/0.42  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 0.21/0.42  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 0.21/0.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.42  fof(t65_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>(k1_relat_1(X1)=k1_xboole_0<=>k2_relat_1(X1)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 0.21/0.42  fof(t118_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k1_relat_1(X3)))=>k9_relat_1(X3,k2_tarski(X1,X2))=k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 0.21/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.21/0.42  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.21/0.42  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 0.21/0.42  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,k1_tarski(esk2_0),esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0))))&(esk3_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.21/0.42  fof(c_0_19, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.21/0.42  fof(c_0_20, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.21/0.42  fof(c_0_21, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.21/0.42  fof(c_0_22, plain, ![X40, X41, X42]:((v4_relat_1(X42,X40)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))&(v5_relat_1(X42,X41)|~m1_subset_1(X42,k1_zfmisc_1(k2_zfmisc_1(X40,X41))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.21/0.42  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk2_0),esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.42  cnf(c_0_25, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.42  cnf(c_0_26, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.21/0.42  fof(c_0_27, plain, ![X27, X28]:(~v1_relat_1(X27)|(~m1_subset_1(X28,k1_zfmisc_1(X27))|v1_relat_1(X28))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.21/0.42  fof(c_0_28, plain, ![X31, X32]:v1_relat_1(k2_zfmisc_1(X31,X32)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.21/0.42  fof(c_0_29, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(X11=X8|X11=X9)|X10!=k2_tarski(X8,X9))&((X12!=X8|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))))&(((esk1_3(X13,X14,X15)!=X13|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14))&(esk1_3(X13,X14,X15)!=X14|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(esk1_3(X13,X14,X15)=X13|esk1_3(X13,X14,X15)=X14)|X15=k2_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.21/0.42  fof(c_0_30, plain, ![X23, X24, X25, X26]:((~r1_tarski(X26,k1_enumset1(X23,X24,X25))|(X26=k1_xboole_0|X26=k1_tarski(X23)|X26=k1_tarski(X24)|X26=k1_tarski(X25)|X26=k2_tarski(X23,X24)|X26=k2_tarski(X24,X25)|X26=k2_tarski(X23,X25)|X26=k1_enumset1(X23,X24,X25)))&((((((((X26!=k1_xboole_0|r1_tarski(X26,k1_enumset1(X23,X24,X25)))&(X26!=k1_tarski(X23)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))&(X26!=k1_tarski(X24)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))&(X26!=k1_tarski(X25)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))&(X26!=k2_tarski(X23,X24)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))&(X26!=k2_tarski(X24,X25)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))&(X26!=k2_tarski(X23,X25)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))&(X26!=k1_enumset1(X23,X24,X25)|r1_tarski(X26,k1_enumset1(X23,X24,X25))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_zfmisc_1])])])).
% 0.21/0.42  fof(c_0_31, plain, ![X29, X30]:((~v4_relat_1(X30,X29)|r1_tarski(k1_relat_1(X30),X29)|~v1_relat_1(X30))&(~r1_tarski(k1_relat_1(X30),X29)|v4_relat_1(X30,X29)|~v1_relat_1(X30))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.21/0.42  cnf(c_0_32, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.21/0.42  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])).
% 0.21/0.42  cnf(c_0_34, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.21/0.42  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.21/0.42  cnf(c_0_36, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.21/0.42  cnf(c_0_37, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|X1=k1_tarski(X3)|X1=k1_tarski(X4)|X1=k2_tarski(X2,X3)|X1=k2_tarski(X3,X4)|X1=k2_tarski(X2,X4)|X1=k1_enumset1(X2,X3,X4)|~r1_tarski(X1,k1_enumset1(X2,X3,X4))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.21/0.42  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.42  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_35])])).
% 0.21/0.42  cnf(c_0_41, plain, (r1_tarski(X1,k1_enumset1(X2,X3,X4))|X1!=k2_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.21/0.42  fof(c_0_42, plain, ![X33, X34]:(~v1_relat_1(X34)|r1_tarski(k9_relat_1(X34,X33),k2_relat_1(X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 0.21/0.42  cnf(c_0_43, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_enumset1(X2,X2,X2,X4)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36, c_0_25]), c_0_26])).
% 0.21/0.42  cnf(c_0_44, plain, (X1=k1_xboole_0|X1=k2_enumset1(X4,X4,X4,X4)|X1=k2_enumset1(X3,X3,X3,X4)|X1=k2_enumset1(X3,X3,X3,X3)|X1=k2_enumset1(X2,X2,X3,X4)|X1=k2_enumset1(X2,X2,X2,X4)|X1=k2_enumset1(X2,X2,X2,X3)|X1=k2_enumset1(X2,X2,X2,X2)|~r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_24]), c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_25]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26]), c_0_26])).
% 0.21/0.42  cnf(c_0_45, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.21/0.42  cnf(c_0_46, plain, (r1_tarski(X1,k2_enumset1(X2,X2,X3,X4))|X1!=k2_enumset1(X2,X2,X2,X3)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_25]), c_0_26]), c_0_26])).
% 0.21/0.42  fof(c_0_47, plain, ![X43, X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k7_relset_1(X43,X44,X45,X46)=k9_relat_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 0.21/0.42  fof(c_0_48, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.42  cnf(c_0_49, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.21/0.42  fof(c_0_50, plain, ![X36]:((k1_relat_1(X36)!=k1_xboole_0|k2_relat_1(X36)=k1_xboole_0|~v1_relat_1(X36))&(k2_relat_1(X36)!=k1_xboole_0|k1_relat_1(X36)=k1_xboole_0|~v1_relat_1(X36))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_relat_1])])])).
% 0.21/0.42  cnf(c_0_51, plain, (r2_hidden(X1,k2_enumset1(X1,X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_43])])).
% 0.21/0.42  cnf(c_0_52, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_relat_1(esk5_0)|k1_relat_1(esk5_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.21/0.42  cnf(c_0_53, plain, (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X2,X3))), inference(er,[status(thm)],[c_0_46])).
% 0.21/0.42  fof(c_0_54, plain, ![X37, X38, X39]:(~v1_relat_1(X39)|~v1_funct_1(X39)|(~r2_hidden(X37,k1_relat_1(X39))|~r2_hidden(X38,k1_relat_1(X39))|k9_relat_1(X39,k2_tarski(X37,X38))=k2_tarski(k1_funct_1(X39,X37),k1_funct_1(X39,X38)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).
% 0.21/0.42  cnf(c_0_55, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk2_0),esk3_0,esk5_0,esk4_0),k1_tarski(k1_funct_1(esk5_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_56, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.21/0.42  cnf(c_0_57, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.21/0.42  cnf(c_0_58, negated_conjecture, (r1_tarski(k9_relat_1(esk5_0,X1),k2_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_49, c_0_40])).
% 0.21/0.42  cnf(c_0_59, plain, (k2_relat_1(X1)=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.21/0.42  cnf(c_0_60, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.42  fof(c_0_61, plain, ![X7]:r1_tarski(k1_xboole_0,X7), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.21/0.42  cnf(c_0_62, negated_conjecture, (k1_relat_1(esk5_0)=k1_xboole_0|r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_53, c_0_52])).
% 0.21/0.42  cnf(c_0_63, plain, (k9_relat_1(X1,k2_tarski(X2,X3))=k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.21/0.42  cnf(c_0_64, negated_conjecture, (~r1_tarski(k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_24]), c_0_24]), c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.21/0.42  cnf(c_0_65, negated_conjecture, (k7_relset_1(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),esk3_0,esk5_0,X1)=k9_relat_1(esk5_0,X1)), inference(spm,[status(thm)],[c_0_56, c_0_33])).
% 0.21/0.42  cnf(c_0_66, negated_conjecture, (k9_relat_1(esk5_0,X1)=k2_relat_1(esk5_0)|~r1_tarski(k2_relat_1(esk5_0),k9_relat_1(esk5_0,X1))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.21/0.42  cnf(c_0_67, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_40])])).
% 0.21/0.42  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.21/0.42  cnf(c_0_69, negated_conjecture, (k2_relat_1(esk5_0)=k1_xboole_0|r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_62]), c_0_40])])).
% 0.21/0.42  cnf(c_0_70, plain, (k9_relat_1(X1,k2_enumset1(X2,X2,X2,X3))=k2_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_25]), c_0_25]), c_0_26]), c_0_26])).
% 0.21/0.42  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.21/0.42  cnf(c_0_72, negated_conjecture, (~r1_tarski(k9_relat_1(esk5_0,esk4_0),k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0)))), inference(rw,[status(thm)],[c_0_64, c_0_65])).
% 0.21/0.42  cnf(c_0_73, negated_conjecture, (k9_relat_1(esk5_0,X1)=k1_xboole_0|r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])])).
% 0.21/0.42  cnf(c_0_74, negated_conjecture, (k9_relat_1(esk5_0,X1)=k1_xboole_0|r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_69]), c_0_68])])).
% 0.21/0.42  fof(c_0_75, plain, ![X35]:(~v1_relat_1(X35)|k9_relat_1(X35,k1_relat_1(X35))=k2_relat_1(X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.21/0.42  cnf(c_0_76, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X1),k1_funct_1(esk5_0,X2))=k9_relat_1(esk5_0,k2_enumset1(X1,X1,X1,X2))|~r2_hidden(X2,k1_relat_1(esk5_0))|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_40])])).
% 0.21/0.42  cnf(c_0_77, negated_conjecture, (r2_hidden(esk2_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_68])])).
% 0.21/0.42  cnf(c_0_78, negated_conjecture, (r1_tarski(k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0),k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_74]), c_0_68])])).
% 0.21/0.42  cnf(c_0_79, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.21/0.42  cnf(c_0_80, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,X1))=k9_relat_1(esk5_0,k2_enumset1(esk2_0,esk2_0,esk2_0,X1))|~r2_hidden(X1,k1_relat_1(esk5_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.42  cnf(c_0_81, negated_conjecture, (k2_enumset1(esk2_0,esk2_0,esk2_0,esk2_0)=k1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_78]), c_0_45])])).
% 0.21/0.42  cnf(c_0_82, negated_conjecture, (k9_relat_1(esk5_0,k1_relat_1(esk5_0))=k2_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_79, c_0_40])).
% 0.21/0.42  cnf(c_0_83, negated_conjecture, (k2_enumset1(k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0),k1_funct_1(esk5_0,esk2_0))=k2_relat_1(esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_77]), c_0_81]), c_0_82])).
% 0.21/0.42  cnf(c_0_84, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_83]), c_0_58])]), ['proof']).
% 0.21/0.42  # SZS output end CNFRefutation
% 0.21/0.42  # Proof object total steps             : 85
% 0.21/0.42  # Proof object clause steps            : 50
% 0.21/0.42  # Proof object formula steps           : 35
% 0.21/0.42  # Proof object conjectures             : 30
% 0.21/0.42  # Proof object clause conjectures      : 27
% 0.21/0.42  # Proof object formula conjectures     : 3
% 0.21/0.42  # Proof object initial clauses used    : 20
% 0.21/0.42  # Proof object initial formulas used   : 17
% 0.21/0.42  # Proof object generating inferences   : 20
% 0.21/0.42  # Proof object simplifying inferences  : 64
% 0.21/0.42  # Training examples: 0 positive, 0 negative
% 0.21/0.42  # Parsed axioms                        : 17
% 0.21/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.42  # Initial clauses                      : 39
% 0.21/0.42  # Removed in clause preprocessing      : 3
% 0.21/0.42  # Initial clauses in saturation        : 36
% 0.21/0.42  # Processed clauses                    : 439
% 0.21/0.42  # ...of these trivial                  : 4
% 0.21/0.42  # ...subsumed                          : 172
% 0.21/0.42  # ...remaining for further processing  : 263
% 0.21/0.42  # Other redundant clauses eliminated   : 106
% 0.21/0.42  # Clauses deleted for lack of memory   : 0
% 0.21/0.42  # Backward-subsumed                    : 25
% 0.21/0.42  # Backward-rewritten                   : 73
% 0.21/0.42  # Generated clauses                    : 1603
% 0.21/0.42  # ...of the previous two non-trivial   : 1131
% 0.21/0.42  # Contextual simplify-reflections      : 2
% 0.21/0.42  # Paramodulations                      : 1439
% 0.21/0.42  # Factorizations                       : 60
% 0.21/0.42  # Equation resolutions                 : 106
% 0.21/0.42  # Propositional unsat checks           : 0
% 0.21/0.42  #    Propositional check models        : 0
% 0.21/0.42  #    Propositional check unsatisfiable : 0
% 0.21/0.42  #    Propositional clauses             : 0
% 0.21/0.42  #    Propositional clauses after purity: 0
% 0.21/0.42  #    Propositional unsat core size     : 0
% 0.21/0.42  #    Propositional preprocessing time  : 0.000
% 0.21/0.42  #    Propositional encoding time       : 0.000
% 0.21/0.42  #    Propositional solver time         : 0.000
% 0.21/0.42  #    Success case prop preproc time    : 0.000
% 0.21/0.42  #    Success case prop encoding time   : 0.000
% 0.21/0.42  #    Success case prop solver time     : 0.000
% 0.21/0.42  # Current number of processed clauses  : 119
% 0.21/0.42  #    Positive orientable unit clauses  : 32
% 0.21/0.42  #    Positive unorientable unit clauses: 0
% 0.21/0.42  #    Negative unit clauses             : 1
% 0.21/0.42  #    Non-unit-clauses                  : 86
% 0.21/0.42  # Current number of unprocessed clauses: 607
% 0.21/0.42  # ...number of literals in the above   : 3969
% 0.21/0.42  # Current number of archived formulas  : 0
% 0.21/0.42  # Current number of archived clauses   : 134
% 0.21/0.42  # Clause-clause subsumption calls (NU) : 5249
% 0.21/0.42  # Rec. Clause-clause subsumption calls : 2104
% 0.21/0.42  # Non-unit clause-clause subsumptions  : 191
% 0.21/0.42  # Unit Clause-clause subsumption calls : 288
% 0.21/0.42  # Rewrite failures with RHS unbound    : 0
% 0.21/0.42  # BW rewrite match attempts            : 65
% 0.21/0.42  # BW rewrite match successes           : 17
% 0.21/0.42  # Condensation attempts                : 0
% 0.21/0.42  # Condensation successes               : 0
% 0.21/0.42  # Termbank termtop insertions          : 40585
% 0.21/0.42  
% 0.21/0.42  # -------------------------------------------------
% 0.21/0.42  # User time                : 0.073 s
% 0.21/0.42  # System time              : 0.007 s
% 0.21/0.42  # Total time               : 0.080 s
% 0.21/0.42  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
