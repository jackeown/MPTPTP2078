%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:04:47 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  123 (1865 expanded)
%              Number of clauses        :   79 ( 845 expanded)
%              Number of leaves         :   22 ( 497 expanded)
%              Depth                    :   19
%              Number of atoms          :  374 (4694 expanded)
%              Number of equality atoms :  133 (1889 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   44 (   2 average)
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

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

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

fof(t144_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(cc3_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_funct_1)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(t205_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k1_relat_1(X2))
      <=> k11_relat_1(X2,X1) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(t147_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X2,k1_relat_1(X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

fof(redefinition_k7_relset_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k7_relset_1(X1,X2,X3,X4) = k9_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(t118_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_relat_1(X3)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X1,k1_relat_1(X3))
          & r2_hidden(X2,k1_relat_1(X3)) )
       => k9_relat_1(X3,k2_tarski(X1,X2)) = k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,k1_tarski(X1),X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))) )
       => ( X2 != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))) ) ) ),
    inference(assume_negation,[status(cth)],[t64_funct_2])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ( k2_zfmisc_1(X22,X23) != k1_xboole_0
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( X22 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 )
      & ( X23 != k1_xboole_0
        | k2_zfmisc_1(X22,X23) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_24,negated_conjecture,
    ( v1_funct_1(esk8_0)
    & v1_funct_2(esk8_0,k1_tarski(esk5_0),esk6_0)
    & m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))
    & esk6_0 != k1_xboole_0
    & ~ r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0))) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

fof(c_0_25,plain,(
    ! [X17] : k2_tarski(X17,X17) = k1_tarski(X17) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_26,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_27,plain,(
    ! [X34,X35] : v1_relat_1(k2_zfmisc_1(X34,X35)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_29,plain,(
    ! [X62,X63,X64] :
      ( ( v4_relat_1(X64,X62)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) )
      & ( v5_relat_1(X64,X63)
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X59,X60,X61] :
      ( ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))
      | v1_relat_1(X61) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_34,plain,(
    ! [X36,X37] :
      ( ~ v1_relat_1(X37)
      | r1_tarski(k9_relat_1(X37,X36),k2_relat_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).

cnf(c_0_35,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ( ~ m1_subset_1(X25,k1_zfmisc_1(X26))
        | r1_tarski(X25,X26) )
      & ( ~ r1_tarski(X25,X26)
        | m1_subset_1(X25,k1_zfmisc_1(X26)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_38,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

fof(c_0_39,plain,(
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

fof(c_0_40,plain,(
    ! [X20,X21] :
      ( ( ~ r1_tarski(X20,k1_tarski(X21))
        | X20 = k1_xboole_0
        | X20 = k1_tarski(X21) )
      & ( X20 != k1_xboole_0
        | r1_tarski(X20,k1_tarski(X21)) )
      & ( X20 != k1_tarski(X21)
        | r1_tarski(X20,k1_tarski(X21)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_41,plain,(
    ! [X32,X33] :
      ( ( ~ v4_relat_1(X33,X32)
        | r1_tarski(k1_relat_1(X33),X32)
        | ~ v1_relat_1(X33) )
      & ( ~ r1_tarski(k1_relat_1(X33),X32)
        | v4_relat_1(X33,X32)
        | ~ v1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_42,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

cnf(c_0_44,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_45,plain,(
    ! [X6,X7] :
      ( ( r1_tarski(X6,X7)
        | X6 != X7 )
      & ( r1_tarski(X7,X6)
        | X6 != X7 )
      & ( ~ r1_tarski(X6,X7)
        | ~ r1_tarski(X7,X6)
        | X6 = X7 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_46,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_48,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_49,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_50,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_51,plain,(
    ! [X30,X31] :
      ( ~ v1_relat_1(X30)
      | k11_relat_1(X30,X31) = k9_relat_1(X30,k1_tarski(X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

fof(c_0_52,plain,(
    ! [X42,X43] :
      ( ~ v1_relat_1(X42)
      | ~ v1_funct_1(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(X42))
      | v1_funct_1(X43) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).

cnf(c_0_53,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_tarski(X2)
    | ~ r1_tarski(X1,k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_55,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_56,negated_conjecture,
    ( v4_relat_1(esk8_0,k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_43])).

cnf(c_0_58,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X1),k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_62,plain,
    ( v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_63,plain,
    ( X1 = X4
    | X1 = X3
    | X2 != k1_enumset1(X3,X3,X4)
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_53,c_0_32])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | X1 = k1_enumset1(X2,X2,X2)
    | ~ r1_tarski(X1,k1_enumset1(X2,X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk8_0),k1_enumset1(esk5_0,esk5_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

fof(c_0_66,plain,(
    ! [X44,X45,X46,X47,X49,X50,X51,X52,X54] :
      ( ( r2_hidden(esk2_4(X44,X45,X46,X47),k1_relat_1(X44))
        | ~ r2_hidden(X47,X46)
        | X46 != k9_relat_1(X44,X45)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( r2_hidden(esk2_4(X44,X45,X46,X47),X45)
        | ~ r2_hidden(X47,X46)
        | X46 != k9_relat_1(X44,X45)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( X47 = k1_funct_1(X44,esk2_4(X44,X45,X46,X47))
        | ~ r2_hidden(X47,X46)
        | X46 != k9_relat_1(X44,X45)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( ~ r2_hidden(X50,k1_relat_1(X44))
        | ~ r2_hidden(X50,X45)
        | X49 != k1_funct_1(X44,X50)
        | r2_hidden(X49,X46)
        | X46 != k9_relat_1(X44,X45)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( ~ r2_hidden(esk3_3(X44,X51,X52),X52)
        | ~ r2_hidden(X54,k1_relat_1(X44))
        | ~ r2_hidden(X54,X51)
        | esk3_3(X44,X51,X52) != k1_funct_1(X44,X54)
        | X52 = k9_relat_1(X44,X51)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( r2_hidden(esk4_3(X44,X51,X52),k1_relat_1(X44))
        | r2_hidden(esk3_3(X44,X51,X52),X52)
        | X52 = k9_relat_1(X44,X51)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( r2_hidden(esk4_3(X44,X51,X52),X51)
        | r2_hidden(esk3_3(X44,X51,X52),X52)
        | X52 = k9_relat_1(X44,X51)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) )
      & ( esk3_3(X44,X51,X52) = k1_funct_1(X44,esk4_3(X44,X51,X52))
        | r2_hidden(esk3_3(X44,X51,X52),X52)
        | X52 = k9_relat_1(X44,X51)
        | ~ v1_relat_1(X44)
        | ~ v1_funct_1(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_67,plain,(
    ! [X40,X41] :
      ( ( ~ r2_hidden(X40,k1_relat_1(X41))
        | k11_relat_1(X41,X40) != k1_xboole_0
        | ~ v1_relat_1(X41) )
      & ( k11_relat_1(X41,X40) = k1_xboole_0
        | r2_hidden(X40,k1_relat_1(X41))
        | ~ v1_relat_1(X41) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).

cnf(c_0_68,plain,
    ( k9_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])])).

cnf(c_0_69,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_enumset1(X2,X2,X2))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_31]),c_0_32])).

cnf(c_0_70,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_50])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_72,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k1_enumset1(X3,X3,X2)) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( k1_enumset1(esk5_0,esk5_0,esk5_0) = k1_relat_1(esk8_0)
    | k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_74,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | k11_relat_1(X2,X1) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_76,plain,
    ( k11_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_48])])).

cnf(c_0_77,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_78,plain,
    ( r2_hidden(esk2_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X2)
    | r2_hidden(esk3_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_81,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | X1 = esk5_0
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk4_3(esk8_0,X2,X1),k1_relat_1(esk8_0))
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_71]),c_0_57])])).

cnf(c_0_83,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_48]),c_0_77])])).

cnf(c_0_84,plain,
    ( r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X3,k9_relat_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79,c_0_57])])).

fof(c_0_86,plain,(
    ! [X38,X39] :
      ( ~ v1_relat_1(X39)
      | r1_tarski(k9_relat_1(X39,X38),k9_relat_1(X39,k1_relat_1(X39))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_relat_1])])).

cnf(c_0_87,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | r2_hidden(esk4_3(esk8_0,X2,X1),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_71]),c_0_57])])).

cnf(c_0_88,negated_conjecture,
    ( esk4_3(esk8_0,X1,X2) = esk5_0
    | X2 = k9_relat_1(esk8_0,X1)
    | k1_relat_1(esk8_0) = k1_xboole_0
    | r2_hidden(esk3_3(esk8_0,X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_89,plain,
    ( ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k9_relat_1(X1,k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_85]),c_0_68]),c_0_77]),c_0_48])]),c_0_83])).

cnf(c_0_91,plain,
    ( r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_92,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | r2_hidden(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( k9_relat_1(X1,k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,k1_relat_1(X1)),k9_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_91])).

cnf(c_0_95,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0
    | k1_relat_1(esk8_0) = k1_xboole_0
    | r2_hidden(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_92])).

cnf(c_0_96,negated_conjecture,
    ( k9_relat_1(esk8_0,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_71]),c_0_57])])).

fof(c_0_97,plain,(
    ! [X65,X66,X67,X68] :
      ( ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))
      | k7_relset_1(X65,X66,X67,X68) = k9_relat_1(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).

cnf(c_0_98,plain,
    ( r1_tarski(k11_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_69])).

cnf(c_0_99,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0
    | k9_relat_1(esk8_0,X2) = k1_xboole_0
    | r2_hidden(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_57]),c_0_96]),c_0_60])])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_101,plain,
    ( k7_relset_1(X2,X3,X1,X4) = k9_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

fof(c_0_102,plain,(
    ! [X56,X57,X58] :
      ( ~ v1_relat_1(X58)
      | ~ v1_funct_1(X58)
      | ~ r2_hidden(X56,k1_relat_1(X58))
      | ~ r2_hidden(X57,k1_relat_1(X58))
      | k9_relat_1(X58,k2_tarski(X56,X57)) = k2_tarski(k1_funct_1(X58,X56),k1_funct_1(X58,X57)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).

cnf(c_0_103,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_104,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k11_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k9_relat_1(X1,k1_relat_1(X1)),k11_relat_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_98])).

cnf(c_0_105,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(esk5_0,X1) ),
    inference(ef,[status(thm)],[c_0_99])).

cnf(c_0_106,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,esk7_0),k1_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100,c_0_31]),c_0_31]),c_0_32]),c_0_32])).

cnf(c_0_107,negated_conjecture,
    ( k7_relset_1(k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,X1) = k9_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_101,c_0_43])).

cnf(c_0_108,plain,
    ( k9_relat_1(X1,k2_tarski(X2,X3)) = k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X3,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_enumset1(X2,X2,X4) ),
    inference(rw,[status(thm)],[c_0_103,c_0_32])).

cnf(c_0_110,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_105]),c_0_57]),c_0_60])])).

cnf(c_0_111,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(esk8_0,esk7_0),k1_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0))) ),
    inference(rw,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_112,plain,
    ( k9_relat_1(X1,k1_enumset1(X2,X2,X3)) = k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108,c_0_32]),c_0_32])).

cnf(c_0_113,plain,
    ( r2_hidden(X1,k1_enumset1(X1,X1,X2)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_109])])).

cnf(c_0_114,negated_conjecture,
    ( r2_hidden(esk5_0,k1_relat_1(esk8_0))
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_110]),c_0_57])])).

cnf(c_0_115,negated_conjecture,
    ( ~ r2_hidden(esk5_0,k1_relat_1(esk8_0))
    | ~ r1_tarski(k9_relat_1(esk8_0,esk7_0),k9_relat_1(esk8_0,k1_enumset1(esk5_0,esk5_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_71]),c_0_57])])).

cnf(c_0_116,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | r2_hidden(esk5_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_113,c_0_73])).

cnf(c_0_117,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk3_3(esk8_0,X2,X1),X1)
    | r2_hidden(esk5_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_82])).

cnf(c_0_118,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0
    | ~ r1_tarski(k9_relat_1(esk8_0,esk7_0),k9_relat_1(esk8_0,k1_relat_1(esk8_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115,c_0_73]),c_0_116])).

cnf(c_0_119,negated_conjecture,
    ( k1_relat_1(esk8_0) = k9_relat_1(esk8_0,X1)
    | r2_hidden(esk5_0,k1_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_117])).

cnf(c_0_120,negated_conjecture,
    ( k1_relat_1(esk8_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118,c_0_91]),c_0_57])])).

cnf(c_0_121,negated_conjecture,
    ( k9_relat_1(esk8_0,X1) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119,c_0_120]),c_0_120]),c_0_83])).

cnf(c_0_122,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111,c_0_121]),c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.07/1.29  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 1.07/1.29  # and selection function SelectMaxLComplexAvoidPosPred.
% 1.07/1.29  #
% 1.07/1.29  # Preprocessing time       : 0.029 s
% 1.07/1.29  
% 1.07/1.29  # Proof found!
% 1.07/1.29  # SZS status Theorem
% 1.07/1.29  # SZS output start CNFRefutation
% 1.07/1.29  fof(t64_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 1.07/1.29  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.07/1.29  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.07/1.29  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.07/1.29  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.07/1.29  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 1.07/1.29  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 1.07/1.29  fof(t144_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k2_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 1.07/1.29  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.07/1.29  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.07/1.29  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.07/1.29  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.07/1.29  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 1.07/1.29  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.07/1.29  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.07/1.29  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 1.07/1.29  fof(cc3_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_funct_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_funct_1)).
% 1.07/1.29  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 1.07/1.29  fof(t205_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k1_relat_1(X2))<=>k11_relat_1(X2,X1)!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 1.07/1.29  fof(t147_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k9_relat_1(X2,X1),k9_relat_1(X2,k1_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 1.07/1.29  fof(redefinition_k7_relset_1, axiom, ![X1, X2, X3, X4]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k7_relset_1(X1,X2,X3,X4)=k9_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 1.07/1.29  fof(t118_funct_1, axiom, ![X1, X2, X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((r2_hidden(X1,k1_relat_1(X3))&r2_hidden(X2,k1_relat_1(X3)))=>k9_relat_1(X3,k2_tarski(X1,X2))=k2_tarski(k1_funct_1(X3,X1),k1_funct_1(X3,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_funct_1)).
% 1.07/1.29  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,k1_tarski(X1),X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X1),X2))))=>(X2!=k1_xboole_0=>r1_tarski(k7_relset_1(k1_tarski(X1),X2,X4,X3),k1_tarski(k1_funct_1(X4,X1)))))), inference(assume_negation,[status(cth)],[t64_funct_2])).
% 1.07/1.29  fof(c_0_23, plain, ![X22, X23]:((k2_zfmisc_1(X22,X23)!=k1_xboole_0|(X22=k1_xboole_0|X23=k1_xboole_0))&((X22!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0)&(X23!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 1.07/1.29  fof(c_0_24, negated_conjecture, (((v1_funct_1(esk8_0)&v1_funct_2(esk8_0,k1_tarski(esk5_0),esk6_0))&m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0))))&(esk6_0!=k1_xboole_0&~r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 1.07/1.29  fof(c_0_25, plain, ![X17]:k2_tarski(X17,X17)=k1_tarski(X17), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.07/1.29  fof(c_0_26, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.07/1.29  fof(c_0_27, plain, ![X34, X35]:v1_relat_1(k2_zfmisc_1(X34,X35)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 1.07/1.29  cnf(c_0_28, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.07/1.29  fof(c_0_29, plain, ![X62, X63, X64]:((v4_relat_1(X64,X62)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))&(v5_relat_1(X64,X63)|~m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(X62,X63))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 1.07/1.29  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(esk5_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.29  cnf(c_0_31, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.07/1.29  cnf(c_0_32, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.07/1.29  fof(c_0_33, plain, ![X59, X60, X61]:(~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X59,X60)))|v1_relat_1(X61)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 1.07/1.29  fof(c_0_34, plain, ![X36, X37]:(~v1_relat_1(X37)|r1_tarski(k9_relat_1(X37,X36),k2_relat_1(X37))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t144_relat_1])])).
% 1.07/1.29  cnf(c_0_35, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.07/1.29  cnf(c_0_36, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 1.07/1.29  fof(c_0_37, plain, ![X25, X26]:((~m1_subset_1(X25,k1_zfmisc_1(X26))|r1_tarski(X25,X26))&(~r1_tarski(X25,X26)|m1_subset_1(X25,k1_zfmisc_1(X26)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 1.07/1.29  fof(c_0_38, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 1.07/1.29  fof(c_0_39, plain, ![X8, X9, X10, X11, X12, X13, X14, X15]:(((~r2_hidden(X11,X10)|(X11=X8|X11=X9)|X10!=k2_tarski(X8,X9))&((X12!=X8|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))&(X12!=X9|r2_hidden(X12,X10)|X10!=k2_tarski(X8,X9))))&(((esk1_3(X13,X14,X15)!=X13|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14))&(esk1_3(X13,X14,X15)!=X14|~r2_hidden(esk1_3(X13,X14,X15),X15)|X15=k2_tarski(X13,X14)))&(r2_hidden(esk1_3(X13,X14,X15),X15)|(esk1_3(X13,X14,X15)=X13|esk1_3(X13,X14,X15)=X14)|X15=k2_tarski(X13,X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 1.07/1.29  fof(c_0_40, plain, ![X20, X21]:((~r1_tarski(X20,k1_tarski(X21))|(X20=k1_xboole_0|X20=k1_tarski(X21)))&((X20!=k1_xboole_0|r1_tarski(X20,k1_tarski(X21)))&(X20!=k1_tarski(X21)|r1_tarski(X20,k1_tarski(X21))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 1.07/1.29  fof(c_0_41, plain, ![X32, X33]:((~v4_relat_1(X33,X32)|r1_tarski(k1_relat_1(X33),X32)|~v1_relat_1(X33))&(~r1_tarski(k1_relat_1(X33),X32)|v4_relat_1(X33,X32)|~v1_relat_1(X33))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 1.07/1.29  cnf(c_0_42, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_29])).
% 1.07/1.29  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk8_0,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 1.07/1.29  cnf(c_0_44, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.07/1.29  fof(c_0_45, plain, ![X6, X7]:(((r1_tarski(X6,X7)|X6!=X7)&(r1_tarski(X7,X6)|X6!=X7))&(~r1_tarski(X6,X7)|~r1_tarski(X7,X6)|X6=X7)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.07/1.29  cnf(c_0_46, plain, (r1_tarski(k9_relat_1(X1,X2),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.07/1.29  cnf(c_0_47, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 1.07/1.29  cnf(c_0_48, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 1.07/1.29  cnf(c_0_49, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 1.07/1.29  cnf(c_0_50, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.07/1.29  fof(c_0_51, plain, ![X30, X31]:(~v1_relat_1(X30)|k11_relat_1(X30,X31)=k9_relat_1(X30,k1_tarski(X31))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 1.07/1.29  fof(c_0_52, plain, ![X42, X43]:(~v1_relat_1(X42)|~v1_funct_1(X42)|(~m1_subset_1(X43,k1_zfmisc_1(X42))|v1_funct_1(X43))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc3_funct_1])])])).
% 1.07/1.29  cnf(c_0_53, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.07/1.29  cnf(c_0_54, plain, (X1=k1_xboole_0|X1=k1_tarski(X2)|~r1_tarski(X1,k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.07/1.29  cnf(c_0_55, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 1.07/1.29  cnf(c_0_56, negated_conjecture, (v4_relat_1(esk8_0,k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 1.07/1.29  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_44, c_0_43])).
% 1.07/1.29  cnf(c_0_58, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.07/1.29  cnf(c_0_59, plain, (r1_tarski(k9_relat_1(k1_xboole_0,X1),k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 1.07/1.29  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 1.07/1.29  cnf(c_0_61, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 1.07/1.29  cnf(c_0_62, plain, (v1_funct_1(X2)|~v1_relat_1(X1)|~v1_funct_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 1.07/1.29  cnf(c_0_63, plain, (X1=X4|X1=X3|X2!=k1_enumset1(X3,X3,X4)|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_53, c_0_32])).
% 1.07/1.29  cnf(c_0_64, plain, (X1=k1_xboole_0|X1=k1_enumset1(X2,X2,X2)|~r1_tarski(X1,k1_enumset1(X2,X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 1.07/1.29  cnf(c_0_65, negated_conjecture, (r1_tarski(k1_relat_1(esk8_0),k1_enumset1(esk5_0,esk5_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 1.07/1.29  fof(c_0_66, plain, ![X44, X45, X46, X47, X49, X50, X51, X52, X54]:(((((r2_hidden(esk2_4(X44,X45,X46,X47),k1_relat_1(X44))|~r2_hidden(X47,X46)|X46!=k9_relat_1(X44,X45)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(r2_hidden(esk2_4(X44,X45,X46,X47),X45)|~r2_hidden(X47,X46)|X46!=k9_relat_1(X44,X45)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(X47=k1_funct_1(X44,esk2_4(X44,X45,X46,X47))|~r2_hidden(X47,X46)|X46!=k9_relat_1(X44,X45)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(~r2_hidden(X50,k1_relat_1(X44))|~r2_hidden(X50,X45)|X49!=k1_funct_1(X44,X50)|r2_hidden(X49,X46)|X46!=k9_relat_1(X44,X45)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&((~r2_hidden(esk3_3(X44,X51,X52),X52)|(~r2_hidden(X54,k1_relat_1(X44))|~r2_hidden(X54,X51)|esk3_3(X44,X51,X52)!=k1_funct_1(X44,X54))|X52=k9_relat_1(X44,X51)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(((r2_hidden(esk4_3(X44,X51,X52),k1_relat_1(X44))|r2_hidden(esk3_3(X44,X51,X52),X52)|X52=k9_relat_1(X44,X51)|(~v1_relat_1(X44)|~v1_funct_1(X44)))&(r2_hidden(esk4_3(X44,X51,X52),X51)|r2_hidden(esk3_3(X44,X51,X52),X52)|X52=k9_relat_1(X44,X51)|(~v1_relat_1(X44)|~v1_funct_1(X44))))&(esk3_3(X44,X51,X52)=k1_funct_1(X44,esk4_3(X44,X51,X52))|r2_hidden(esk3_3(X44,X51,X52),X52)|X52=k9_relat_1(X44,X51)|(~v1_relat_1(X44)|~v1_funct_1(X44)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 1.07/1.29  fof(c_0_67, plain, ![X40, X41]:((~r2_hidden(X40,k1_relat_1(X41))|k11_relat_1(X41,X40)!=k1_xboole_0|~v1_relat_1(X41))&(k11_relat_1(X41,X40)=k1_xboole_0|r2_hidden(X40,k1_relat_1(X41))|~v1_relat_1(X41))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t205_relat_1])])])).
% 1.07/1.29  cnf(c_0_68, plain, (k9_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])])).
% 1.07/1.29  cnf(c_0_69, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_enumset1(X2,X2,X2))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_31]), c_0_32])).
% 1.07/1.29  cnf(c_0_70, plain, (v1_funct_1(k1_xboole_0)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_62, c_0_50])).
% 1.07/1.29  cnf(c_0_71, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.29  cnf(c_0_72, plain, (X1=X2|X1=X3|~r2_hidden(X1,k1_enumset1(X3,X3,X2))), inference(er,[status(thm)],[c_0_63])).
% 1.07/1.29  cnf(c_0_73, negated_conjecture, (k1_enumset1(esk5_0,esk5_0,esk5_0)=k1_relat_1(esk8_0)|k1_relat_1(esk8_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 1.07/1.29  cnf(c_0_74, plain, (r2_hidden(esk4_3(X1,X2,X3),k1_relat_1(X1))|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.07/1.29  cnf(c_0_75, plain, (~r2_hidden(X1,k1_relat_1(X2))|k11_relat_1(X2,X1)!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 1.07/1.29  cnf(c_0_76, plain, (k11_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_48])])).
% 1.07/1.29  cnf(c_0_77, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 1.07/1.29  cnf(c_0_78, plain, (r2_hidden(esk2_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.07/1.29  cnf(c_0_79, negated_conjecture, (v1_funct_1(k1_xboole_0)|~v1_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 1.07/1.29  cnf(c_0_80, plain, (r2_hidden(esk4_3(X1,X2,X3),X2)|r2_hidden(esk3_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 1.07/1.29  cnf(c_0_81, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|X1=esk5_0|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_72, c_0_73])).
% 1.07/1.29  cnf(c_0_82, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk4_3(esk8_0,X2,X1),k1_relat_1(esk8_0))|r2_hidden(esk3_3(esk8_0,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_71]), c_0_57])])).
% 1.07/1.29  cnf(c_0_83, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_48]), c_0_77])])).
% 1.07/1.29  cnf(c_0_84, plain, (r2_hidden(esk2_4(X1,X2,k9_relat_1(X1,X2),X3),X2)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X3,k9_relat_1(X1,X2))), inference(er,[status(thm)],[c_0_78])).
% 1.07/1.29  cnf(c_0_85, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_79, c_0_57])])).
% 1.07/1.29  fof(c_0_86, plain, ![X38, X39]:(~v1_relat_1(X39)|r1_tarski(k9_relat_1(X39,X38),k9_relat_1(X39,k1_relat_1(X39)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t147_relat_1])])).
% 1.07/1.29  cnf(c_0_87, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|r2_hidden(esk4_3(esk8_0,X2,X1),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_71]), c_0_57])])).
% 1.07/1.29  cnf(c_0_88, negated_conjecture, (esk4_3(esk8_0,X1,X2)=esk5_0|X2=k9_relat_1(esk8_0,X1)|k1_relat_1(esk8_0)=k1_xboole_0|r2_hidden(esk3_3(esk8_0,X1,X2),X2)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 1.07/1.29  cnf(c_0_89, plain, (~v1_funct_1(X1)|~v1_relat_1(X1)|~r2_hidden(X2,k9_relat_1(X1,k1_xboole_0))), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 1.07/1.29  cnf(c_0_90, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_3(k1_xboole_0,X2,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_85]), c_0_68]), c_0_77]), c_0_48])]), c_0_83])).
% 1.07/1.29  cnf(c_0_91, plain, (r1_tarski(k9_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_86])).
% 1.07/1.29  cnf(c_0_92, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|r2_hidden(esk5_0,X2)), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 1.07/1.29  cnf(c_0_93, negated_conjecture, (k9_relat_1(X1,k1_xboole_0)=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.07/1.29  cnf(c_0_94, plain, (k9_relat_1(X1,k1_relat_1(X1))=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,k1_relat_1(X1)),k9_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_91])).
% 1.07/1.29  cnf(c_0_95, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0|k1_relat_1(esk8_0)=k1_xboole_0|r2_hidden(esk5_0,X1)), inference(spm,[status(thm)],[c_0_83, c_0_92])).
% 1.07/1.29  cnf(c_0_96, negated_conjecture, (k9_relat_1(esk8_0,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_71]), c_0_57])])).
% 1.07/1.29  fof(c_0_97, plain, ![X65, X66, X67, X68]:(~m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(X65,X66)))|k7_relset_1(X65,X66,X67,X68)=k9_relat_1(X67,X68)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k7_relset_1])])).
% 1.07/1.29  cnf(c_0_98, plain, (r1_tarski(k11_relat_1(X1,X2),k9_relat_1(X1,k1_relat_1(X1)))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_91, c_0_69])).
% 1.07/1.29  cnf(c_0_99, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0|k9_relat_1(esk8_0,X2)=k1_xboole_0|r2_hidden(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_96]), c_0_57]), c_0_96]), c_0_60])])).
% 1.07/1.29  cnf(c_0_100, negated_conjecture, (~r1_tarski(k7_relset_1(k1_tarski(esk5_0),esk6_0,esk8_0,esk7_0),k1_tarski(k1_funct_1(esk8_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 1.07/1.29  cnf(c_0_101, plain, (k7_relset_1(X2,X3,X1,X4)=k9_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_97])).
% 1.07/1.29  fof(c_0_102, plain, ![X56, X57, X58]:(~v1_relat_1(X58)|~v1_funct_1(X58)|(~r2_hidden(X56,k1_relat_1(X58))|~r2_hidden(X57,k1_relat_1(X58))|k9_relat_1(X58,k2_tarski(X56,X57))=k2_tarski(k1_funct_1(X58,X56),k1_funct_1(X58,X57)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t118_funct_1])])).
% 1.07/1.29  cnf(c_0_103, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 1.07/1.29  cnf(c_0_104, plain, (k9_relat_1(X1,k1_relat_1(X1))=k11_relat_1(X1,X2)|~v1_relat_1(X1)|~r1_tarski(k9_relat_1(X1,k1_relat_1(X1)),k11_relat_1(X1,X2))), inference(spm,[status(thm)],[c_0_58, c_0_98])).
% 1.07/1.29  cnf(c_0_105, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(esk5_0,X1)), inference(ef,[status(thm)],[c_0_99])).
% 1.07/1.29  cnf(c_0_106, negated_conjecture, (~r1_tarski(k7_relset_1(k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,esk7_0),k1_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_100, c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 1.07/1.29  cnf(c_0_107, negated_conjecture, (k7_relset_1(k1_enumset1(esk5_0,esk5_0,esk5_0),esk6_0,esk8_0,X1)=k9_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_101, c_0_43])).
% 1.07/1.29  cnf(c_0_108, plain, (k9_relat_1(X1,k2_tarski(X2,X3))=k2_tarski(k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X3,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 1.07/1.29  cnf(c_0_109, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_enumset1(X2,X2,X4)), inference(rw,[status(thm)],[c_0_103, c_0_32])).
% 1.07/1.29  cnf(c_0_110, negated_conjecture, (k11_relat_1(esk8_0,X1)=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_105]), c_0_57]), c_0_60])])).
% 1.07/1.29  cnf(c_0_111, negated_conjecture, (~r1_tarski(k9_relat_1(esk8_0,esk7_0),k1_enumset1(k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0),k1_funct_1(esk8_0,esk5_0)))), inference(rw,[status(thm)],[c_0_106, c_0_107])).
% 1.07/1.29  cnf(c_0_112, plain, (k9_relat_1(X1,k1_enumset1(X2,X2,X3))=k1_enumset1(k1_funct_1(X1,X2),k1_funct_1(X1,X2),k1_funct_1(X1,X3))|~v1_relat_1(X1)|~v1_funct_1(X1)|~r2_hidden(X3,k1_relat_1(X1))|~r2_hidden(X2,k1_relat_1(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_108, c_0_32]), c_0_32])).
% 1.07/1.29  cnf(c_0_113, plain, (r2_hidden(X1,k1_enumset1(X1,X1,X2))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_109])])).
% 1.07/1.29  cnf(c_0_114, negated_conjecture, (r2_hidden(esk5_0,k1_relat_1(esk8_0))|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_110]), c_0_57])])).
% 1.07/1.29  cnf(c_0_115, negated_conjecture, (~r2_hidden(esk5_0,k1_relat_1(esk8_0))|~r1_tarski(k9_relat_1(esk8_0,esk7_0),k9_relat_1(esk8_0,k1_enumset1(esk5_0,esk5_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_71]), c_0_57])])).
% 1.07/1.29  cnf(c_0_116, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|r2_hidden(esk5_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_113, c_0_73])).
% 1.07/1.29  cnf(c_0_117, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk3_3(esk8_0,X2,X1),X1)|r2_hidden(esk5_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_114, c_0_82])).
% 1.07/1.29  cnf(c_0_118, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0|~r1_tarski(k9_relat_1(esk8_0,esk7_0),k9_relat_1(esk8_0,k1_relat_1(esk8_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_115, c_0_73]), c_0_116])).
% 1.07/1.29  cnf(c_0_119, negated_conjecture, (k1_relat_1(esk8_0)=k9_relat_1(esk8_0,X1)|r2_hidden(esk5_0,k1_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_114, c_0_117])).
% 1.07/1.29  cnf(c_0_120, negated_conjecture, (k1_relat_1(esk8_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_118, c_0_91]), c_0_57])])).
% 1.07/1.29  cnf(c_0_121, negated_conjecture, (k9_relat_1(esk8_0,X1)=k1_xboole_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_119, c_0_120]), c_0_120]), c_0_83])).
% 1.07/1.29  cnf(c_0_122, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_111, c_0_121]), c_0_60])]), ['proof']).
% 1.07/1.29  # SZS output end CNFRefutation
% 1.07/1.29  # Proof object total steps             : 123
% 1.07/1.29  # Proof object clause steps            : 79
% 1.07/1.29  # Proof object formula steps           : 44
% 1.07/1.29  # Proof object conjectures             : 37
% 1.07/1.29  # Proof object clause conjectures      : 34
% 1.07/1.29  # Proof object formula conjectures     : 3
% 1.07/1.29  # Proof object initial clauses used    : 28
% 1.07/1.29  # Proof object initial formulas used   : 22
% 1.07/1.29  # Proof object generating inferences   : 36
% 1.07/1.29  # Proof object simplifying inferences  : 68
% 1.07/1.29  # Training examples: 0 positive, 0 negative
% 1.07/1.29  # Parsed axioms                        : 23
% 1.07/1.29  # Removed by relevancy pruning/SinE    : 0
% 1.07/1.29  # Initial clauses                      : 50
% 1.07/1.29  # Removed in clause preprocessing      : 2
% 1.07/1.29  # Initial clauses in saturation        : 48
% 1.07/1.29  # Processed clauses                    : 4822
% 1.07/1.29  # ...of these trivial                  : 11
% 1.07/1.29  # ...subsumed                          : 3735
% 1.07/1.29  # ...remaining for further processing  : 1076
% 1.07/1.29  # Other redundant clauses eliminated   : 87
% 1.07/1.29  # Clauses deleted for lack of memory   : 0
% 1.07/1.29  # Backward-subsumed                    : 162
% 1.07/1.29  # Backward-rewritten                   : 217
% 1.07/1.29  # Generated clauses                    : 65723
% 1.07/1.29  # ...of the previous two non-trivial   : 56499
% 1.07/1.29  # Contextual simplify-reflections      : 49
% 1.07/1.29  # Paramodulations                      : 65599
% 1.07/1.29  # Factorizations                       : 40
% 1.07/1.29  # Equation resolutions                 : 87
% 1.07/1.29  # Propositional unsat checks           : 0
% 1.07/1.29  #    Propositional check models        : 0
% 1.07/1.29  #    Propositional check unsatisfiable : 0
% 1.07/1.29  #    Propositional clauses             : 0
% 1.07/1.29  #    Propositional clauses after purity: 0
% 1.07/1.29  #    Propositional unsat core size     : 0
% 1.07/1.29  #    Propositional preprocessing time  : 0.000
% 1.07/1.29  #    Propositional encoding time       : 0.000
% 1.07/1.29  #    Propositional solver time         : 0.000
% 1.07/1.29  #    Success case prop preproc time    : 0.000
% 1.07/1.29  #    Success case prop encoding time   : 0.000
% 1.07/1.29  #    Success case prop solver time     : 0.000
% 1.07/1.29  # Current number of processed clauses  : 684
% 1.07/1.29  #    Positive orientable unit clauses  : 53
% 1.07/1.29  #    Positive unorientable unit clauses: 0
% 1.07/1.29  #    Negative unit clauses             : 3
% 1.07/1.29  #    Non-unit-clauses                  : 628
% 1.07/1.29  # Current number of unprocessed clauses: 49229
% 1.07/1.29  # ...number of literals in the above   : 296342
% 1.07/1.29  # Current number of archived formulas  : 0
% 1.07/1.29  # Current number of archived clauses   : 381
% 1.07/1.29  # Clause-clause subsumption calls (NU) : 276423
% 1.07/1.29  # Rec. Clause-clause subsumption calls : 142548
% 1.07/1.29  # Non-unit clause-clause subsumptions  : 2914
% 1.07/1.29  # Unit Clause-clause subsumption calls : 3256
% 1.07/1.29  # Rewrite failures with RHS unbound    : 0
% 1.07/1.29  # BW rewrite match attempts            : 57
% 1.07/1.29  # BW rewrite match successes           : 14
% 1.07/1.29  # Condensation attempts                : 0
% 1.07/1.29  # Condensation successes               : 0
% 1.07/1.29  # Termbank termtop insertions          : 1449210
% 1.07/1.29  
% 1.07/1.29  # -------------------------------------------------
% 1.07/1.29  # User time                : 0.927 s
% 1.07/1.29  # System time              : 0.029 s
% 1.07/1.29  # Total time               : 0.956 s
% 1.07/1.29  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
