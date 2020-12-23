%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:05:42 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 208 expanded)
%              Number of clauses        :   41 (  81 expanded)
%              Number of leaves         :   15 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  183 ( 654 expanded)
%              Number of equality atoms :   74 ( 310 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t73_funct_2,conjecture,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
         => ( ( k2_relset_1(X1,X1,X2) = X1
              & k2_relset_1(X1,X1,X3) = X1 )
           => k2_relset_1(X1,X1,k4_relset_1(X1,X1,X1,X1,X3,X2)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(dt_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(t47_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k1_relat_1(X1),k2_relat_1(X2))
           => k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(t193_relat_1,axiom,(
    ! [X1,X2] : r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t25_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
              & r1_tarski(k2_relat_1(X1),k2_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(t195_relat_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
            & k2_relat_1(k2_zfmisc_1(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

fof(redefinition_k4_relset_1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => k4_relset_1(X1,X2,X3,X4,X5,X6) = k5_relat_1(X5,X6) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
           => ( ( k2_relset_1(X1,X1,X2) = X1
                & k2_relset_1(X1,X1,X3) = X1 )
             => k2_relset_1(X1,X1,k4_relset_1(X1,X1,X1,X1,X3,X2)) = X1 ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_funct_2])).

fof(c_0_16,plain,(
    ! [X15,X16,X17] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(X15))
      | ~ r2_hidden(X17,X16)
      | r2_hidden(X17,X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_17,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))
    & k2_relset_1(esk2_0,esk2_0,esk3_0) = esk2_0
    & k2_relset_1(esk2_0,esk2_0,esk4_0) = esk2_0
    & k2_relset_1(esk2_0,esk2_0,k4_relset_1(esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk3_0)) != esk2_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k2_relset_1(X38,X39,X40) = k2_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

fof(c_0_19,plain,(
    ! [X32,X33,X34,X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))
      | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))
      | m1_subset_1(k4_relset_1(X32,X33,X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(X32,X35))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).

fof(c_0_20,plain,(
    ! [X26,X27] :
      ( ~ v1_relat_1(X26)
      | ~ v1_relat_1(X27)
      | ~ r1_tarski(k1_relat_1(X26),k2_relat_1(X27))
      | k2_relat_1(k5_relat_1(X27,X26)) = k2_relat_1(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).

fof(c_0_21,plain,(
    ! [X20,X21] : r1_tarski(k1_relat_1(k2_zfmisc_1(X20,X21)),X20) ),
    inference(variable_rename,[status(thm)],[t193_relat_1])).

fof(c_0_22,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_23,plain,(
    ! [X29,X30,X31] :
      ( ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))
      | v1_relat_1(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_24,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_27,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k2_relat_1(k5_relat_1(X2,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( k2_relset_1(esk2_0,esk2_0,esk4_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_35,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(k1_relat_1(X24),k1_relat_1(X25))
        | ~ r1_tarski(X24,X25)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) )
      & ( r1_tarski(k2_relat_1(X24),k2_relat_1(X25))
        | ~ r1_tarski(X24,X25)
        | ~ v1_relat_1(X25)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).

fof(c_0_37,plain,(
    ! [X22,X23] :
      ( ( k1_relat_1(k2_zfmisc_1(X22,X23)) = X22
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 )
      & ( k2_relat_1(k2_zfmisc_1(X22,X23)) = X23
        | X22 = k1_xboole_0
        | X23 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,esk2_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( k2_relset_1(esk2_0,esk2_0,k4_relset_1(esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk3_0)) != esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_41,plain,
    ( k2_relset_1(X1,X2,k4_relset_1(X1,X3,X4,X2,X5,X6)) = k2_relat_1(k4_relset_1(X1,X3,X4,X2,X5,X6))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

fof(c_0_42,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))
      | k4_relset_1(X41,X42,X43,X44,X45,X46) = k5_relat_1(X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).

fof(c_0_43,plain,(
    ! [X28] :
      ( ( k1_relat_1(X28) != k1_xboole_0
        | X28 = k1_xboole_0
        | ~ v1_relat_1(X28) )
      & ( k2_relat_1(X28) != k1_xboole_0
        | X28 = k1_xboole_0
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_44,negated_conjecture,
    ( k2_relset_1(esk2_0,esk2_0,esk3_0) = esk2_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_45,plain,
    ( k2_relat_1(k5_relat_1(X1,k2_zfmisc_1(k2_relat_1(X1),X2))) = k2_relat_1(k2_zfmisc_1(k2_relat_1(X1),X2))
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_46,negated_conjecture,
    ( k2_relat_1(esk4_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_32]),c_0_33])).

cnf(c_0_47,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_32])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( r1_tarski(k1_relat_1(X1),k1_relat_1(X2))
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,plain,
    ( k1_relat_1(k2_zfmisc_1(X1,X2)) = X1
    | X1 = k1_xboole_0
    | X2 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk2_0))
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(esk2_0,esk2_0)),esk3_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( k2_relat_1(k4_relset_1(esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk3_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_26]),c_0_32])])).

cnf(c_0_54,plain,
    ( k4_relset_1(X2,X3,X5,X6,X1,X4) = k5_relat_1(X1,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_56,negated_conjecture,
    ( k2_relat_1(esk3_0) = esk2_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_44])).

cnf(c_0_57,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_26])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,k2_zfmisc_1(esk2_0,X1))) = k2_relat_1(k2_zfmisc_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_59,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_60,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_61,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | r1_tarski(k1_relat_1(X3),X1)
    | ~ v1_relat_1(X3)
    | ~ r1_tarski(X3,k2_zfmisc_1(X1,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_31])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(esk3_0,k2_zfmisc_1(esk2_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_63,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,esk3_0)) != esk2_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_32])])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])])).

cnf(c_0_65,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_66,negated_conjecture,
    ( k2_relat_1(k5_relat_1(esk4_0,X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_46]),c_0_47])])).

cnf(c_0_67,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | r1_tarski(k1_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_57])])).

cnf(c_0_68,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_69,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_66]),c_0_56]),c_0_57])])).

cnf(c_0_70,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_67,c_0_68]),c_0_69]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.19/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.030 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t73_funct_2, conjecture, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>((k2_relset_1(X1,X1,X2)=X1&k2_relset_1(X1,X1,X3)=X1)=>k2_relset_1(X1,X1,k4_relset_1(X1,X1,X1,X1,X3,X2))=X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 0.19/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.19/0.39  fof(dt_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>m1_subset_1(k4_relset_1(X1,X2,X3,X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X1,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 0.19/0.39  fof(t47_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(k1_relat_1(X1),k2_relat_1(X2))=>k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 0.19/0.39  fof(t193_relat_1, axiom, ![X1, X2]:r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 0.19/0.39  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.39  fof(t25_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>(r1_tarski(k1_relat_1(X1),k1_relat_1(X2))&r1_tarski(k2_relat_1(X1),k2_relat_1(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 0.19/0.39  fof(t195_relat_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&~((k1_relat_1(k2_zfmisc_1(X1,X2))=X1&k2_relat_1(k2_zfmisc_1(X1,X2))=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 0.19/0.39  fof(redefinition_k4_relset_1, axiom, ![X1, X2, X3, X4, X5, X6]:((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))))=>k4_relset_1(X1,X2,X3,X4,X5,X6)=k5_relat_1(X5,X6)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 0.19/0.39  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.19/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))=>((k2_relset_1(X1,X1,X2)=X1&k2_relset_1(X1,X1,X3)=X1)=>k2_relset_1(X1,X1,k4_relset_1(X1,X1,X1,X1,X3,X2))=X1)))), inference(assume_negation,[status(cth)],[t73_funct_2])).
% 0.19/0.39  fof(c_0_16, plain, ![X15, X16, X17]:(~m1_subset_1(X16,k1_zfmisc_1(X15))|(~r2_hidden(X17,X16)|r2_hidden(X17,X15))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.39  fof(c_0_17, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))&(m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))&((k2_relset_1(esk2_0,esk2_0,esk3_0)=esk2_0&k2_relset_1(esk2_0,esk2_0,esk4_0)=esk2_0)&k2_relset_1(esk2_0,esk2_0,k4_relset_1(esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk3_0))!=esk2_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.19/0.39  fof(c_0_18, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k2_relset_1(X38,X39,X40)=k2_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.19/0.39  fof(c_0_19, plain, ![X32, X33, X34, X35, X36, X37]:(~m1_subset_1(X36,k1_zfmisc_1(k2_zfmisc_1(X32,X33)))|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X34,X35)))|m1_subset_1(k4_relset_1(X32,X33,X34,X35,X36,X37),k1_zfmisc_1(k2_zfmisc_1(X32,X35)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_relset_1])])).
% 0.19/0.39  fof(c_0_20, plain, ![X26, X27]:(~v1_relat_1(X26)|(~v1_relat_1(X27)|(~r1_tarski(k1_relat_1(X26),k2_relat_1(X27))|k2_relat_1(k5_relat_1(X27,X26))=k2_relat_1(X26)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t47_relat_1])])])).
% 0.19/0.39  fof(c_0_21, plain, ![X20, X21]:r1_tarski(k1_relat_1(k2_zfmisc_1(X20,X21)),X20), inference(variable_rename,[status(thm)],[t193_relat_1])).
% 0.19/0.39  fof(c_0_22, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.39  fof(c_0_23, plain, ![X29, X30, X31]:(~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X29,X30)))|v1_relat_1(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.39  fof(c_0_24, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_27, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_28, plain, (m1_subset_1(k4_relset_1(X2,X3,X5,X6,X1,X4),k1_zfmisc_1(k2_zfmisc_1(X2,X6)))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_29, plain, (k2_relat_1(k5_relat_1(X2,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(k1_relat_1(X1),k2_relat_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_30, plain, (r1_tarski(k1_relat_1(k2_zfmisc_1(X1,X2)),X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.39  cnf(c_0_31, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (k2_relset_1(esk2_0,esk2_0,esk4_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_34, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  fof(c_0_35, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.39  fof(c_0_36, plain, ![X24, X25]:((r1_tarski(k1_relat_1(X24),k1_relat_1(X25))|~r1_tarski(X24,X25)|~v1_relat_1(X25)|~v1_relat_1(X24))&(r1_tarski(k2_relat_1(X24),k2_relat_1(X25))|~r1_tarski(X24,X25)|~v1_relat_1(X25)|~v1_relat_1(X24))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t25_relat_1])])])])).
% 0.19/0.39  fof(c_0_37, plain, ![X22, X23]:((k1_relat_1(k2_zfmisc_1(X22,X23))=X22|(X22=k1_xboole_0|X23=k1_xboole_0))&(k2_relat_1(k2_zfmisc_1(X22,X23))=X23|(X22=k1_xboole_0|X23=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t195_relat_1])])])).
% 0.19/0.39  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_39, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk2_0,esk2_0))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_40, negated_conjecture, (k2_relset_1(esk2_0,esk2_0,k4_relset_1(esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk3_0))!=esk2_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_41, plain, (k2_relset_1(X1,X2,k4_relset_1(X1,X3,X4,X2,X5,X6))=k2_relat_1(k4_relset_1(X1,X3,X4,X2,X5,X6))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.39  fof(c_0_42, plain, ![X41, X42, X43, X44, X45, X46]:(~m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44)))|k4_relset_1(X41,X42,X43,X44,X45,X46)=k5_relat_1(X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_relset_1])])).
% 0.19/0.39  fof(c_0_43, plain, ![X28]:((k1_relat_1(X28)!=k1_xboole_0|X28=k1_xboole_0|~v1_relat_1(X28))&(k2_relat_1(X28)!=k1_xboole_0|X28=k1_xboole_0|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.19/0.39  cnf(c_0_44, negated_conjecture, (k2_relset_1(esk2_0,esk2_0,esk3_0)=esk2_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_45, plain, (k2_relat_1(k5_relat_1(X1,k2_zfmisc_1(k2_relat_1(X1),X2)))=k2_relat_1(k2_zfmisc_1(k2_relat_1(X1),X2))|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (k2_relat_1(esk4_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_32]), c_0_33])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_34, c_0_32])).
% 0.19/0.39  cnf(c_0_48, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_49, plain, (r1_tarski(k1_relat_1(X1),k1_relat_1(X2))|~r1_tarski(X1,X2)|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  cnf(c_0_50, plain, (k1_relat_1(k2_zfmisc_1(X1,X2))=X1|X1=k1_xboole_0|X2=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk2_0))|~r2_hidden(esk1_2(X1,k2_zfmisc_1(esk2_0,esk2_0)),esk3_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (k2_relat_1(k4_relset_1(esk2_0,esk2_0,esk2_0,esk2_0,esk4_0,esk3_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_26]), c_0_32])])).
% 0.19/0.39  cnf(c_0_54, plain, (k4_relset_1(X2,X3,X5,X6,X1,X4)=k5_relat_1(X1,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_55, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, (k2_relat_1(esk3_0)=esk2_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_44])).
% 0.19/0.39  cnf(c_0_57, negated_conjecture, (v1_relat_1(esk3_0)), inference(spm,[status(thm)],[c_0_34, c_0_26])).
% 0.19/0.39  cnf(c_0_58, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,k2_zfmisc_1(esk2_0,X1)))=k2_relat_1(k2_zfmisc_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.19/0.39  cnf(c_0_59, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_60, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.39  cnf(c_0_61, plain, (X1=k1_xboole_0|X2=k1_xboole_0|r1_tarski(k1_relat_1(X3),X1)|~v1_relat_1(X3)|~r1_tarski(X3,k2_zfmisc_1(X1,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_31])])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (r1_tarski(esk3_0,k2_zfmisc_1(esk2_0,esk2_0))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.39  cnf(c_0_63, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,esk3_0))!=esk2_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_26]), c_0_32])])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (esk3_0=k1_xboole_0|esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])])).
% 0.19/0.39  cnf(c_0_65, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60])).
% 0.19/0.39  cnf(c_0_66, negated_conjecture, (k2_relat_1(k5_relat_1(esk4_0,X1))=k2_relat_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_46]), c_0_47])])).
% 0.19/0.39  cnf(c_0_67, negated_conjecture, (esk2_0=k1_xboole_0|r1_tarski(k1_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_57])])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (esk2_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (~r1_tarski(k1_relat_1(esk3_0),esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_66]), c_0_56]), c_0_57])])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[c_0_67, c_0_68]), c_0_69]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 71
% 0.19/0.39  # Proof object clause steps            : 41
% 0.19/0.39  # Proof object formula steps           : 30
% 0.19/0.39  # Proof object conjectures             : 25
% 0.19/0.39  # Proof object clause conjectures      : 22
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 20
% 0.19/0.39  # Proof object initial formulas used   : 15
% 0.19/0.39  # Proof object generating inferences   : 19
% 0.19/0.39  # Proof object simplifying inferences  : 29
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 15
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 27
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 27
% 0.19/0.39  # Processed clauses                    : 225
% 0.19/0.39  # ...of these trivial                  : 1
% 0.19/0.39  # ...subsumed                          : 48
% 0.19/0.39  # ...remaining for further processing  : 175
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 1
% 0.19/0.39  # Generated clauses                    : 464
% 0.19/0.39  # ...of the previous two non-trivial   : 377
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 455
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 138
% 0.19/0.39  #    Positive orientable unit clauses  : 26
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 6
% 0.19/0.39  #    Non-unit-clauses                  : 106
% 0.19/0.39  # Current number of unprocessed clauses: 206
% 0.19/0.39  # ...number of literals in the above   : 927
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 35
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 974
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 539
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 45
% 0.19/0.39  # Unit Clause-clause subsumption calls : 127
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 9
% 0.19/0.39  # BW rewrite match successes           : 1
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 10070
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.047 s
% 0.19/0.39  # System time              : 0.003 s
% 0.19/0.39  # Total time               : 0.049 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
