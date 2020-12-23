%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:08 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :  208 (5911 expanded)
%              Number of clauses        :  174 (2801 expanded)
%              Number of leaves         :   17 (1502 expanded)
%              Depth                    :   23
%              Number of atoms          :  553 (18777 expanded)
%              Number of equality atoms :   83 (1248 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_2)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(t12_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => r2_hidden(X2,k1_funct_2(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

fof(c_0_18,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_20,plain,(
    ! [X28,X29] :
      ( ( ~ m1_subset_1(X28,k1_zfmisc_1(X29))
        | r1_tarski(X28,X29) )
      & ( ~ r1_tarski(X28,X29)
        | m1_subset_1(X28,k1_zfmisc_1(X29)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_21,negated_conjecture,
    ( v1_funct_1(esk6_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    & ~ r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X25,X24)
        | r2_hidden(X25,X24)
        | v1_xboole_0(X24) )
      & ( ~ r2_hidden(X25,X24)
        | m1_subset_1(X25,X24)
        | v1_xboole_0(X24) )
      & ( ~ m1_subset_1(X25,X24)
        | v1_xboole_0(X25)
        | ~ v1_xboole_0(X24) )
      & ( ~ v1_xboole_0(X25)
        | m1_subset_1(X25,X24)
        | ~ v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

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

fof(c_0_24,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_25,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X19,X20,X21] :
      ( ~ r1_tarski(X19,X20)
      | ~ r1_tarski(X20,X21)
      | r1_tarski(X19,X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_30,plain,(
    ! [X33,X34,X35] :
      ( ~ v1_xboole_0(X33)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33)))
      | v1_xboole_0(X35) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_31,plain,(
    ! [X44,X45,X46,X47] :
      ( ( v1_funct_1(X47)
        | ~ r2_hidden(X47,k5_partfun1(X44,X45,X46))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( v1_funct_2(X47,X44,X45)
        | ~ r2_hidden(X47,k5_partfun1(X44,X45,X46))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))
        | ~ r2_hidden(X47,k5_partfun1(X44,X45,X46))
        | ~ v1_funct_1(X46)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_34,plain,(
    ! [X26] : ~ v1_xboole_0(k1_zfmisc_1(X26)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,plain,
    ( r1_tarski(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(esk2_2(X1,X2),X2) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_47,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_36,c_0_25])).

fof(c_0_51,plain,(
    ! [X15] :
      ( X15 = k1_xboole_0
      | r2_hidden(esk3_1(X15),X15) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_52,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v1_xboole_0(k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k5_partfun1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_33])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_38])).

fof(c_0_60,plain,(
    ! [X27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(esk2_2(X1,k1_zfmisc_1(X2)),X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_42]),c_0_47])).

cnf(c_0_62,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_48]),c_0_49])])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_26])).

cnf(c_0_64,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_65,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_56])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ m1_subset_1(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_29]),c_0_58])]),c_0_59])).

cnf(c_0_69,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = esk6_0
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_40])).

cnf(c_0_71,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(esk2_2(X1,k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_38])).

cnf(c_0_72,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)
    | v1_xboole_0(esk2_2(k1_zfmisc_1(k1_xboole_0),X1)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_73,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ r1_tarski(esk2_2(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))),esk6_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_53])).

cnf(c_0_74,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)
    | r1_tarski(k1_zfmisc_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_28,c_0_63])).

cnf(c_0_75,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ r1_tarski(X1,esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( r1_tarski(esk1_1(k1_zfmisc_1(X1)),X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_67]),c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r1_tarski(X2,esk6_0)
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_53])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ m1_subset_1(esk2_2(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))),k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_68]),c_0_47])).

cnf(c_0_80,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_69])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ m1_subset_1(X1,k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_68])).

cnf(c_0_82,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = esk6_0
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_38])).

cnf(c_0_83,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_85,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66])).

cnf(c_0_86,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = esk1_1(k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_77])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_63])).

cnf(c_0_89,plain,
    ( esk2_2(k1_zfmisc_1(k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k1_zfmisc_1(k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_72])).

cnf(c_0_90,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = X1
    | ~ r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)
    | ~ r1_tarski(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_53])).

cnf(c_0_91,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = k1_xboole_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_80])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0)),k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_67]),c_0_59])).

cnf(c_0_93,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,esk5_0) = esk6_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_82,c_0_66])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_83])).

cnf(c_0_95,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_96,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_86])).

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_87])).

cnf(c_0_98,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_99,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_88,c_0_85])).

cnf(c_0_100,plain,
    ( r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_89])).

cnf(c_0_101,negated_conjecture,
    ( k1_xboole_0 = X1
    | ~ r1_tarski(X1,esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_80])])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0)),esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_92,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))),X1)
    | v1_xboole_0(esk2_2(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))),X1))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_96,c_0_63])).

cnf(c_0_105,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_38])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(esk1_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_97,c_0_55])).

cnf(c_0_107,plain,
    ( v1_xboole_0(X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_62,c_0_42])).

cnf(c_0_108,plain,
    ( r1_tarski(esk1_1(k1_zfmisc_1(X1)),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_98,c_0_77])).

cnf(c_0_109,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_110,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_80])).

cnf(c_0_111,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_94,c_0_99])).

cnf(c_0_113,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_39,c_0_100])).

cnf(c_0_114,negated_conjecture,
    ( esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0)) = k1_xboole_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_115,negated_conjecture,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(esk6_0)
    | ~ r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_103])).

cnf(c_0_116,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_71,c_0_104])).

cnf(c_0_117,negated_conjecture,
    ( X1 = esk1_1(k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_105,c_0_106])).

cnf(c_0_118,plain,
    ( v1_xboole_0(esk1_1(k1_zfmisc_1(X1)))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_107,c_0_108])).

cnf(c_0_119,plain,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(X1,X2)),X3)
    | v1_xboole_0(esk2_2(k1_zfmisc_1(k2_zfmisc_1(X1,X2)),X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_63])).

cnf(c_0_120,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_109,c_0_83])).

cnf(c_0_121,plain,
    ( esk1_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_110,c_0_77])).

cnf(c_0_122,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k5_partfun1(X2,X3,X4)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_33])).

cnf(c_0_123,negated_conjecture,
    ( k1_zfmisc_1(X1) = k5_partfun1(esk4_0,esk5_0,esk6_0)
    | ~ r1_tarski(k1_zfmisc_1(X1),k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_112])).

cnf(c_0_124,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk6_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_113,c_0_103])).

cnf(c_0_125,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_114]),c_0_59])).

cnf(c_0_126,negated_conjecture,
    ( k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))) = k1_zfmisc_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_115,c_0_116])).

cnf(c_0_127,negated_conjecture,
    ( esk1_1(k1_zfmisc_1(X1)) = esk1_1(k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_117,c_0_118])).

cnf(c_0_128,plain,
    ( X1 = k1_zfmisc_1(k1_xboole_0)
    | ~ r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_100])).

cnf(c_0_129,plain,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_71,c_0_119])).

cnf(c_0_130,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_56]),c_0_121]),c_0_47])).

cnf(c_0_131,plain,
    ( esk1_1(k1_zfmisc_1(X1)) = X2
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_108])).

cnf(c_0_132,plain,
    ( v1_funct_1(X1)
    | v1_xboole_0(k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X1,k5_partfun1(X2,X3,X4))
    | ~ r1_tarski(X4,k2_zfmisc_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_122,c_0_42])).

cnf(c_0_133,negated_conjecture,
    ( k5_partfun1(esk4_0,esk5_0,esk6_0) = k1_zfmisc_1(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_124]),c_0_125])).

cnf(c_0_134,negated_conjecture,
    ( k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))) = k1_zfmisc_1(esk6_0)
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_127])).

cnf(c_0_135,plain,
    ( esk1_1(k1_zfmisc_1(X1)) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_77])).

cnf(c_0_136,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X1,X2)) = k1_zfmisc_1(k1_xboole_0)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_129]),c_0_130])])).

cnf(c_0_137,plain,
    ( esk1_1(k1_zfmisc_1(X1)) = k2_zfmisc_1(X2,X3)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_131,c_0_66])).

cnf(c_0_138,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(X2))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_77])).

cnf(c_0_139,plain,
    ( esk2_2(k1_zfmisc_1(X1),X2) = X1
    | r1_tarski(k1_zfmisc_1(X1),X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_52,c_0_74])).

cnf(c_0_140,negated_conjecture,
    ( esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0)) = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_92])).

fof(c_0_141,plain,(
    ! [X39,X40,X41] :
      ( ( X40 = k1_xboole_0
        | r2_hidden(X41,k1_funct_2(X39,X40))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) )
      & ( X39 != k1_xboole_0
        | r2_hidden(X41,k1_funct_2(X39,X40))
        | ~ v1_funct_1(X41)
        | ~ v1_funct_2(X41,X39,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_142,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_143,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132,c_0_133]),c_0_58]),c_0_40])]),c_0_47])).

cnf(c_0_144,negated_conjecture,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(esk6_0)
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_145,plain,
    ( k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))) = k1_zfmisc_1(k1_xboole_0)
    | ~ v1_xboole_0(X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_136,c_0_137])).

cnf(c_0_146,plain,
    ( r1_tarski(esk2_2(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))),X2),X1)
    | r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))),X2) ),
    inference(spm,[status(thm)],[c_0_138,c_0_74])).

cnf(c_0_147,negated_conjecture,
    ( k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)) = k5_partfun1(esk4_0,esk5_0,esk6_0)
    | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)),k5_partfun1(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_88])).

cnf(c_0_148,plain,
    ( r1_tarski(k1_zfmisc_1(X1),X2)
    | ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_139])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(k2_zfmisc_1(esk4_0,esk5_0),k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_140]),c_0_59])).

cnf(c_0_150,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_98,c_0_40])).

cnf(c_0_151,negated_conjecture,
    ( X1 = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_87])).

cnf(c_0_152,negated_conjecture,
    ( v1_xboole_0(esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_29])).

cnf(c_0_153,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_141])).

cnf(c_0_154,plain,
    ( m1_subset_1(esk2_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_26])).

cnf(c_0_155,plain,
    ( v1_funct_1(esk2_2(k5_partfun1(X1,X2,X3),X4))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_111,c_0_26])).

cnf(c_0_156,plain,
    ( v1_funct_2(esk2_2(k5_partfun1(X1,X2,X3),X4),X1,X2)
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_26])).

cnf(c_0_157,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_143,c_0_144])).

cnf(c_0_158,plain,
    ( k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))) = k1_zfmisc_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_145,c_0_49])).

cnf(c_0_159,plain,
    ( r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_146])).

cnf(c_0_160,negated_conjecture,
    ( k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)) = k5_partfun1(esk4_0,esk5_0,esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_149])).

cnf(c_0_161,negated_conjecture,
    ( r1_tarski(esk6_0,X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_150,c_0_66])).

cnf(c_0_162,negated_conjecture,
    ( X1 = esk6_0
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_93]),c_0_152])).

cnf(c_0_163,plain,
    ( r1_tarski(esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1)))),X1) ),
    inference(spm,[status(thm)],[c_0_138,c_0_77])).

fof(c_0_164,plain,(
    ! [X36,X37,X38] :
      ( v1_xboole_0(X36)
      | ~ v1_xboole_0(X37)
      | ~ v1_funct_1(X38)
      | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
      | v1_xboole_0(k5_partfun1(X36,X37,X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

cnf(c_0_165,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k5_partfun1(X2,X1,X3),X4)
    | r2_hidden(esk2_2(k5_partfun1(X2,X1,X3),X4),k1_funct_2(X2,X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_155]),c_0_156])).

cnf(c_0_166,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_157,c_0_42])).

cnf(c_0_167,plain,
    ( k1_zfmisc_1(X1) = k1_zfmisc_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_158,c_0_135])).

cnf(c_0_168,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0))),k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_159,c_0_160])).

cnf(c_0_169,negated_conjecture,
    ( X1 = esk6_0
    | ~ r1_tarski(X1,esk6_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_161])).

cnf(c_0_170,negated_conjecture,
    ( X1 = esk6_0
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_162,c_0_127])).

cnf(c_0_171,negated_conjecture,
    ( esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0)))) = k2_zfmisc_1(esk4_0,esk5_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_163])).

cnf(c_0_172,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_164])).

cnf(c_0_173,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k5_partfun1(X2,X1,X3),k1_funct_2(X2,X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_32,c_0_165])).

cnf(c_0_174,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_87]),c_0_66])).

cnf(c_0_175,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_88,c_0_167])).

cnf(c_0_176,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)),k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_168,c_0_140])).

cnf(c_0_177,negated_conjecture,
    ( esk2_2(k1_zfmisc_1(esk6_0),X1) = esk6_0
    | r1_tarski(k1_zfmisc_1(esk6_0),X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_169,c_0_74])).

cnf(c_0_178,negated_conjecture,
    ( X1 = esk6_0
    | ~ r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170,c_0_171]),c_0_106])).

cnf(c_0_179,negated_conjecture,
    ( v1_xboole_0(esk4_0)
    | ~ v1_xboole_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172,c_0_29]),c_0_58])]),c_0_59])).

cnf(c_0_180,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_173]),c_0_58]),c_0_29])])).

fof(c_0_181,plain,(
    ! [X42,X43] :
      ( ~ v1_funct_1(X43)
      | ~ v1_funct_2(X43,X42,X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42)))
      | r2_hidden(X43,k1_funct_2(X42,X42)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).

cnf(c_0_182,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(X1,esk1_1(k1_zfmisc_1(X2)))
    | ~ v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_174,c_0_144])).

cnf(c_0_183,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(X1))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_175])).

cnf(c_0_184,negated_conjecture,
    ( r1_tarski(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_176])).

cnf(c_0_185,negated_conjecture,
    ( ~ r1_tarski(k1_zfmisc_1(esk6_0),k1_funct_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_133])).

cnf(c_0_186,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk6_0),X1)
    | ~ r2_hidden(esk6_0,X1)
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_177])).

cnf(c_0_187,negated_conjecture,
    ( esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))) = esk6_0
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_178,c_0_163])).

cnf(c_0_188,negated_conjecture,
    ( v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_179,c_0_180]),c_0_49])])).

cnf(c_0_189,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_181])).

cnf(c_0_190,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_171]),c_0_106])).

cnf(c_0_191,negated_conjecture,
    ( k1_zfmisc_1(X1) = k5_partfun1(esk4_0,esk5_0,esk6_0)
    | ~ r1_tarski(k1_zfmisc_1(X1),k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_183])).

cnf(c_0_192,negated_conjecture,
    ( r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))),k5_partfun1(esk4_0,esk5_0,esk6_0))
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_184,c_0_159])).

cnf(c_0_193,negated_conjecture,
    ( ~ r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_185,c_0_186])).

cnf(c_0_194,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187,c_0_180]),c_0_48]),c_0_121]),c_0_121]),c_0_180]),c_0_49])])).

cnf(c_0_195,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_75,c_0_188])).

cnf(c_0_196,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v1_funct_1(X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X2)) ),
    inference(spm,[status(thm)],[c_0_189,c_0_42])).

cnf(c_0_197,negated_conjecture,
    ( v1_funct_1(esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))))
    | ~ v1_xboole_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_190,c_0_163])).

cnf(c_0_198,negated_conjecture,
    ( k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))) = k5_partfun1(esk4_0,esk5_0,esk6_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_191,c_0_192])).

cnf(c_0_199,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_200,negated_conjecture,
    ( ~ r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_193,c_0_180]),c_0_180]),c_0_49])]),c_0_194]),c_0_195])).

cnf(c_0_201,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_2(X1,X2,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_196,c_0_38])).

cnf(c_0_202,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_197,c_0_180]),c_0_48]),c_0_121]),c_0_121]),c_0_180]),c_0_49])])).

cnf(c_0_203,plain,
    ( v1_funct_2(esk1_1(k5_partfun1(X1,X2,X3)),X1,X2)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_142,c_0_56])).

cnf(c_0_204,negated_conjecture,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_zfmisc_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_198,c_0_180]),c_0_48]),c_0_121]),c_0_180]),c_0_180]),c_0_48]),c_0_49])]),c_0_195]),c_0_194])).

cnf(c_0_205,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_199])).

cnf(c_0_206,negated_conjecture,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_201]),c_0_202]),c_0_49])])).

cnf(c_0_207,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_204]),c_0_121]),c_0_202]),c_0_205]),c_0_69])]),c_0_206]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 3.38/3.55  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 3.38/3.55  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.38/3.55  #
% 3.38/3.55  # Preprocessing time       : 0.028 s
% 3.38/3.55  
% 3.38/3.55  # Proof found!
% 3.38/3.55  # SZS status Theorem
% 3.38/3.55  # SZS output start CNFRefutation
% 3.38/3.55  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 3.38/3.55  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/3.55  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.38/3.55  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.38/3.55  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.38/3.55  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.38/3.55  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/3.55  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.38/3.55  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.38/3.55  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 3.38/3.55  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.38/3.55  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.38/3.55  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.38/3.55  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.38/3.55  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 3.38/3.55  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 3.38/3.55  fof(t12_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>r2_hidden(X2,k1_funct_2(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_2)).
% 3.38/3.55  fof(c_0_17, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 3.38/3.55  fof(c_0_18, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 3.38/3.55  fof(c_0_19, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.38/3.55  fof(c_0_20, plain, ![X28, X29]:((~m1_subset_1(X28,k1_zfmisc_1(X29))|r1_tarski(X28,X29))&(~r1_tarski(X28,X29)|m1_subset_1(X28,k1_zfmisc_1(X29)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.38/3.55  fof(c_0_21, negated_conjecture, ((v1_funct_1(esk6_0)&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))&~r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 3.38/3.55  fof(c_0_22, plain, ![X24, X25]:(((~m1_subset_1(X25,X24)|r2_hidden(X25,X24)|v1_xboole_0(X24))&(~r2_hidden(X25,X24)|m1_subset_1(X25,X24)|v1_xboole_0(X24)))&((~m1_subset_1(X25,X24)|v1_xboole_0(X25)|~v1_xboole_0(X24))&(~v1_xboole_0(X25)|m1_subset_1(X25,X24)|~v1_xboole_0(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 3.38/3.55  fof(c_0_23, plain, ![X22, X23]:((k2_zfmisc_1(X22,X23)!=k1_xboole_0|(X22=k1_xboole_0|X23=k1_xboole_0))&((X22!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0)&(X23!=k1_xboole_0|k2_zfmisc_1(X22,X23)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 3.38/3.55  fof(c_0_24, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 3.38/3.55  cnf(c_0_25, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.38/3.55  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.38/3.55  fof(c_0_27, plain, ![X19, X20, X21]:(~r1_tarski(X19,X20)|~r1_tarski(X20,X21)|r1_tarski(X19,X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 3.38/3.55  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.38/3.55  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.38/3.55  fof(c_0_30, plain, ![X33, X34, X35]:(~v1_xboole_0(X33)|(~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X33)))|v1_xboole_0(X35))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 3.38/3.55  fof(c_0_31, plain, ![X44, X45, X46, X47]:(((v1_funct_1(X47)|~r2_hidden(X47,k5_partfun1(X44,X45,X46))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&(v1_funct_2(X47,X44,X45)|~r2_hidden(X47,k5_partfun1(X44,X45,X46))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&(m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))|~r2_hidden(X47,k5_partfun1(X44,X45,X46))|(~v1_funct_1(X46)|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 3.38/3.55  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.38/3.55  cnf(c_0_33, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.38/3.55  fof(c_0_34, plain, ![X26]:~v1_xboole_0(k1_zfmisc_1(X26)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 3.38/3.55  cnf(c_0_35, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.38/3.55  cnf(c_0_36, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.38/3.55  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.38/3.55  cnf(c_0_38, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 3.38/3.55  cnf(c_0_39, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 3.38/3.55  cnf(c_0_40, negated_conjecture, (r1_tarski(esk6_0,k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 3.38/3.55  cnf(c_0_41, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.38/3.55  cnf(c_0_42, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.38/3.55  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_24])).
% 3.38/3.55  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.38/3.55  cnf(c_0_45, negated_conjecture, (~r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_funct_2(esk4_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.38/3.55  cnf(c_0_46, plain, (r1_tarski(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(esk2_2(X1,X2),X2)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 3.38/3.55  cnf(c_0_47, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 3.38/3.55  cnf(c_0_48, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_35])).
% 3.38/3.55  cnf(c_0_49, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 3.38/3.55  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_36, c_0_25])).
% 3.38/3.55  fof(c_0_51, plain, ![X15]:(X15=k1_xboole_0|r2_hidden(esk3_1(X15),X15)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 3.38/3.55  cnf(c_0_52, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 3.38/3.55  cnf(c_0_53, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 3.38/3.55  cnf(c_0_54, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 3.38/3.55  cnf(c_0_55, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 3.38/3.55  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 3.38/3.55  cnf(c_0_57, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|v1_xboole_0(k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k5_partfun1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_44, c_0_33])).
% 3.38/3.55  cnf(c_0_58, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.38/3.55  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_45, c_0_38])).
% 3.38/3.55  fof(c_0_60, plain, ![X27]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X27)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 3.38/3.55  cnf(c_0_61, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(esk2_2(X1,k1_zfmisc_1(X2)),X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_42]), c_0_47])).
% 3.38/3.55  cnf(c_0_62, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_48]), c_0_49])])).
% 3.38/3.55  cnf(c_0_63, plain, (m1_subset_1(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_50, c_0_26])).
% 3.38/3.55  cnf(c_0_64, plain, (X1=k1_xboole_0|r2_hidden(esk3_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.38/3.55  cnf(c_0_65, negated_conjecture, (X1=k2_zfmisc_1(esk4_0,esk5_0)|~r1_tarski(X1,esk6_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 3.38/3.55  cnf(c_0_66, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 3.38/3.55  cnf(c_0_67, plain, (m1_subset_1(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_50, c_0_56])).
% 3.38/3.55  cnf(c_0_68, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~m1_subset_1(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_29]), c_0_58])]), c_0_59])).
% 3.38/3.55  cnf(c_0_69, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 3.38/3.55  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=esk6_0|~r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_40])).
% 3.38/3.55  cnf(c_0_71, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~v1_xboole_0(esk2_2(X1,k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_61, c_0_38])).
% 3.38/3.55  cnf(c_0_72, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)|v1_xboole_0(esk2_2(k1_zfmisc_1(k1_xboole_0),X1))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 3.38/3.55  cnf(c_0_73, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~r1_tarski(esk2_2(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))),esk6_0)), inference(spm,[status(thm)],[c_0_61, c_0_53])).
% 3.38/3.55  cnf(c_0_74, plain, (r1_tarski(esk2_2(k1_zfmisc_1(X1),X2),X1)|r1_tarski(k1_zfmisc_1(X1),X2)), inference(spm,[status(thm)],[c_0_28, c_0_63])).
% 3.38/3.55  cnf(c_0_75, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_25, c_0_64])).
% 3.38/3.55  cnf(c_0_76, negated_conjecture, (X1=k2_zfmisc_1(esk4_0,esk5_0)|~r1_tarski(X1,esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 3.38/3.55  cnf(c_0_77, plain, (r1_tarski(esk1_1(k1_zfmisc_1(X1)),X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_67]), c_0_47])).
% 3.38/3.55  cnf(c_0_78, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r1_tarski(X2,esk6_0)|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_39, c_0_53])).
% 3.38/3.55  cnf(c_0_79, negated_conjecture, (r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~m1_subset_1(esk2_2(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))),k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_68]), c_0_47])).
% 3.38/3.55  cnf(c_0_80, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_28, c_0_69])).
% 3.38/3.55  cnf(c_0_81, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~m1_subset_1(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_28, c_0_68])).
% 3.38/3.55  cnf(c_0_82, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=esk6_0|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_70, c_0_38])).
% 3.38/3.55  cnf(c_0_83, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 3.38/3.55  cnf(c_0_84, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 3.38/3.55  cnf(c_0_85, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_75, c_0_66])).
% 3.38/3.55  cnf(c_0_86, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=esk1_1(k1_zfmisc_1(esk6_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 3.38/3.55  cnf(c_0_87, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))), inference(spm,[status(thm)],[c_0_78, c_0_77])).
% 3.38/3.55  cnf(c_0_88, negated_conjecture, (r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_79, c_0_63])).
% 3.38/3.55  cnf(c_0_89, plain, (esk2_2(k1_zfmisc_1(k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_75, c_0_72])).
% 3.38/3.55  cnf(c_0_90, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=X1|~r1_tarski(k2_zfmisc_1(esk4_0,esk5_0),X1)|~r1_tarski(X1,esk6_0)), inference(spm,[status(thm)],[c_0_37, c_0_53])).
% 3.38/3.55  cnf(c_0_91, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=k1_xboole_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_80])).
% 3.38/3.55  cnf(c_0_92, negated_conjecture, (r1_tarski(esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0)),k2_zfmisc_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_67]), c_0_59])).
% 3.38/3.55  cnf(c_0_93, negated_conjecture, (k2_zfmisc_1(esk4_0,esk5_0)=esk6_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_82, c_0_66])).
% 3.38/3.55  cnf(c_0_94, plain, (r1_tarski(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_39, c_0_83])).
% 3.38/3.55  cnf(c_0_95, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 3.38/3.55  cnf(c_0_96, negated_conjecture, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_86])).
% 3.38/3.55  cnf(c_0_97, negated_conjecture, (v1_xboole_0(X1)|~r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_87])).
% 3.38/3.55  cnf(c_0_98, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 3.38/3.55  cnf(c_0_99, negated_conjecture, (r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_88, c_0_85])).
% 3.38/3.55  cnf(c_0_100, plain, (r1_tarski(k1_zfmisc_1(k1_xboole_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_89])).
% 3.38/3.55  cnf(c_0_101, negated_conjecture, (k1_xboole_0=X1|~r1_tarski(X1,esk6_0)|~v1_xboole_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_91]), c_0_80])])).
% 3.38/3.55  cnf(c_0_102, negated_conjecture, (r1_tarski(esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0)),esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_92, c_0_93])).
% 3.38/3.55  cnf(c_0_103, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk6_0),k1_zfmisc_1(X1))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_95])).
% 3.38/3.55  cnf(c_0_104, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))),X1)|v1_xboole_0(esk2_2(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))),X1))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_96, c_0_63])).
% 3.38/3.55  cnf(c_0_105, plain, (X1=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_38])).
% 3.38/3.55  cnf(c_0_106, negated_conjecture, (v1_xboole_0(esk1_1(k1_zfmisc_1(esk6_0)))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_97, c_0_55])).
% 3.38/3.55  cnf(c_0_107, plain, (v1_xboole_0(X1)|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_62, c_0_42])).
% 3.38/3.55  cnf(c_0_108, plain, (r1_tarski(esk1_1(k1_zfmisc_1(X1)),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_98, c_0_77])).
% 3.38/3.55  cnf(c_0_109, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 3.38/3.55  cnf(c_0_110, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_37, c_0_80])).
% 3.38/3.55  cnf(c_0_111, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.38/3.55  cnf(c_0_112, negated_conjecture, (r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(X1))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_94, c_0_99])).
% 3.38/3.55  cnf(c_0_113, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_39, c_0_100])).
% 3.38/3.55  cnf(c_0_114, negated_conjecture, (esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0))=k1_xboole_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 3.38/3.55  cnf(c_0_115, negated_conjecture, (k1_zfmisc_1(X1)=k1_zfmisc_1(esk6_0)|~r1_tarski(k1_zfmisc_1(X1),k1_zfmisc_1(esk6_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_103])).
% 3.38/3.55  cnf(c_0_116, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))),k1_zfmisc_1(X1))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_71, c_0_104])).
% 3.38/3.55  cnf(c_0_117, negated_conjecture, (X1=esk1_1(k1_zfmisc_1(esk6_0))|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_105, c_0_106])).
% 3.38/3.55  cnf(c_0_118, plain, (v1_xboole_0(esk1_1(k1_zfmisc_1(X1)))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_107, c_0_108])).
% 3.38/3.55  cnf(c_0_119, plain, (r1_tarski(k1_zfmisc_1(k2_zfmisc_1(X1,X2)),X3)|v1_xboole_0(esk2_2(k1_zfmisc_1(k2_zfmisc_1(X1,X2)),X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_63])).
% 3.38/3.55  cnf(c_0_120, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_109, c_0_83])).
% 3.38/3.55  cnf(c_0_121, plain, (esk1_1(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(spm,[status(thm)],[c_0_110, c_0_77])).
% 3.38/3.55  cnf(c_0_122, plain, (v1_funct_1(X1)|v1_xboole_0(k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~m1_subset_1(X1,k5_partfun1(X2,X3,X4))), inference(spm,[status(thm)],[c_0_111, c_0_33])).
% 3.38/3.55  cnf(c_0_123, negated_conjecture, (k1_zfmisc_1(X1)=k5_partfun1(esk4_0,esk5_0,esk6_0)|~r1_tarski(k1_zfmisc_1(X1),k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_112])).
% 3.38/3.55  cnf(c_0_124, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk6_0),X1)|~r2_hidden(k1_xboole_0,X1)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_113, c_0_103])).
% 3.38/3.55  cnf(c_0_125, negated_conjecture, (r2_hidden(k1_xboole_0,k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_114]), c_0_59])).
% 3.38/3.55  cnf(c_0_126, negated_conjecture, (k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0)))=k1_zfmisc_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_115, c_0_116])).
% 3.38/3.55  cnf(c_0_127, negated_conjecture, (esk1_1(k1_zfmisc_1(X1))=esk1_1(k1_zfmisc_1(esk6_0))|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_117, c_0_118])).
% 3.38/3.55  cnf(c_0_128, plain, (X1=k1_zfmisc_1(k1_xboole_0)|~r1_tarski(X1,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_37, c_0_100])).
% 3.38/3.55  cnf(c_0_129, plain, (r1_tarski(k1_zfmisc_1(k2_zfmisc_1(X1,X2)),k1_zfmisc_1(X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_71, c_0_119])).
% 3.38/3.55  cnf(c_0_130, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120, c_0_56]), c_0_121]), c_0_47])).
% 3.38/3.55  cnf(c_0_131, plain, (esk1_1(k1_zfmisc_1(X1))=X2|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_108])).
% 3.38/3.55  cnf(c_0_132, plain, (v1_funct_1(X1)|v1_xboole_0(k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X1,k5_partfun1(X2,X3,X4))|~r1_tarski(X4,k2_zfmisc_1(X2,X3))), inference(spm,[status(thm)],[c_0_122, c_0_42])).
% 3.38/3.55  cnf(c_0_133, negated_conjecture, (k5_partfun1(esk4_0,esk5_0,esk6_0)=k1_zfmisc_1(esk6_0)|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_123, c_0_124]), c_0_125])).
% 3.38/3.55  cnf(c_0_134, negated_conjecture, (k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1)))=k1_zfmisc_1(esk6_0)|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_126, c_0_127])).
% 3.38/3.55  cnf(c_0_135, plain, (esk1_1(k1_zfmisc_1(X1))=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_77])).
% 3.38/3.55  cnf(c_0_136, plain, (k1_zfmisc_1(k2_zfmisc_1(X1,X2))=k1_zfmisc_1(k1_xboole_0)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128, c_0_129]), c_0_130])])).
% 3.38/3.55  cnf(c_0_137, plain, (esk1_1(k1_zfmisc_1(X1))=k2_zfmisc_1(X2,X3)|~v1_xboole_0(X1)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_131, c_0_66])).
% 3.38/3.55  cnf(c_0_138, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,esk1_1(k1_zfmisc_1(X2)))), inference(spm,[status(thm)],[c_0_39, c_0_77])).
% 3.38/3.55  cnf(c_0_139, plain, (esk2_2(k1_zfmisc_1(X1),X2)=X1|r1_tarski(k1_zfmisc_1(X1),X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_52, c_0_74])).
% 3.38/3.55  cnf(c_0_140, negated_conjecture, (esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0))=k2_zfmisc_1(esk4_0,esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_92])).
% 3.38/3.55  fof(c_0_141, plain, ![X39, X40, X41]:((X40=k1_xboole_0|r2_hidden(X41,k1_funct_2(X39,X40))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))&(X39!=k1_xboole_0|r2_hidden(X41,k1_funct_2(X39,X40))|(~v1_funct_1(X41)|~v1_funct_2(X41,X39,X40)|~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 3.38/3.55  cnf(c_0_142, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_31])).
% 3.38/3.55  cnf(c_0_143, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(esk6_0))|~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_132, c_0_133]), c_0_58]), c_0_40])]), c_0_47])).
% 3.38/3.55  cnf(c_0_144, negated_conjecture, (k1_zfmisc_1(X1)=k1_zfmisc_1(esk6_0)|~v1_xboole_0(esk5_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_134, c_0_135])).
% 3.38/3.55  cnf(c_0_145, plain, (k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1)))=k1_zfmisc_1(k1_xboole_0)|~v1_xboole_0(X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_136, c_0_137])).
% 3.38/3.55  cnf(c_0_146, plain, (r1_tarski(esk2_2(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))),X2),X1)|r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))),X2)), inference(spm,[status(thm)],[c_0_138, c_0_74])).
% 3.38/3.55  cnf(c_0_147, negated_conjecture, (k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))=k5_partfun1(esk4_0,esk5_0,esk6_0)|~r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)),k5_partfun1(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_37, c_0_88])).
% 3.38/3.55  cnf(c_0_148, plain, (r1_tarski(k1_zfmisc_1(X1),X2)|~r2_hidden(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_139])).
% 3.38/3.55  cnf(c_0_149, negated_conjecture, (r2_hidden(k2_zfmisc_1(esk4_0,esk5_0),k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_140]), c_0_59])).
% 3.38/3.55  cnf(c_0_150, negated_conjecture, (r1_tarski(esk6_0,X1)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_98, c_0_40])).
% 3.38/3.55  cnf(c_0_151, negated_conjecture, (X1=k2_zfmisc_1(esk4_0,esk5_0)|~r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_52, c_0_87])).
% 3.38/3.55  cnf(c_0_152, negated_conjecture, (v1_xboole_0(esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_41, c_0_29])).
% 3.38/3.55  cnf(c_0_153, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_141])).
% 3.38/3.55  cnf(c_0_154, plain, (m1_subset_1(esk2_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_44, c_0_26])).
% 3.38/3.55  cnf(c_0_155, plain, (v1_funct_1(esk2_2(k5_partfun1(X1,X2,X3),X4))|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_111, c_0_26])).
% 3.38/3.55  cnf(c_0_156, plain, (v1_funct_2(esk2_2(k5_partfun1(X1,X2,X3),X4),X1,X2)|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_142, c_0_26])).
% 3.38/3.55  cnf(c_0_157, negated_conjecture, (v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~v1_xboole_0(esk5_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_143, c_0_144])).
% 3.38/3.55  cnf(c_0_158, plain, (k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1)))=k1_zfmisc_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_145, c_0_49])).
% 3.38/3.55  cnf(c_0_159, plain, (r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1))),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_61, c_0_146])).
% 3.38/3.55  cnf(c_0_160, negated_conjecture, (k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))=k5_partfun1(esk4_0,esk5_0,esk6_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_147, c_0_148]), c_0_149])).
% 3.38/3.55  cnf(c_0_161, negated_conjecture, (r1_tarski(esk6_0,X1)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_150, c_0_66])).
% 3.38/3.55  cnf(c_0_162, negated_conjecture, (X1=esk6_0|~r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_151, c_0_93]), c_0_152])).
% 3.38/3.55  cnf(c_0_163, plain, (r1_tarski(esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(X1)))),X1)), inference(spm,[status(thm)],[c_0_138, c_0_77])).
% 3.38/3.55  fof(c_0_164, plain, ![X36, X37, X38]:(v1_xboole_0(X36)|~v1_xboole_0(X37)|~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|v1_xboole_0(k5_partfun1(X36,X37,X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 3.38/3.55  cnf(c_0_165, plain, (X1=k1_xboole_0|r1_tarski(k5_partfun1(X2,X1,X3),X4)|r2_hidden(esk2_2(k5_partfun1(X2,X1,X3),X4),k1_funct_2(X2,X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_153, c_0_154]), c_0_155]), c_0_156])).
% 3.38/3.55  cnf(c_0_166, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(X1,X2)|~v1_xboole_0(esk5_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_157, c_0_42])).
% 3.38/3.55  cnf(c_0_167, plain, (k1_zfmisc_1(X1)=k1_zfmisc_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_158, c_0_135])).
% 3.38/3.55  cnf(c_0_168, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk1_1(k5_partfun1(esk4_0,esk5_0,esk6_0))),k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_159, c_0_160])).
% 3.38/3.55  cnf(c_0_169, negated_conjecture, (X1=esk6_0|~r1_tarski(X1,esk6_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_161])).
% 3.38/3.55  cnf(c_0_170, negated_conjecture, (X1=esk6_0|~r1_tarski(X1,esk1_1(k1_zfmisc_1(X2)))|~v1_xboole_0(esk5_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_162, c_0_127])).
% 3.38/3.55  cnf(c_0_171, negated_conjecture, (esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(esk6_0))))=k2_zfmisc_1(esk4_0,esk5_0)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_76, c_0_163])).
% 3.38/3.55  cnf(c_0_172, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_164])).
% 3.38/3.55  cnf(c_0_173, plain, (X1=k1_xboole_0|r1_tarski(k5_partfun1(X2,X1,X3),k1_funct_2(X2,X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_32, c_0_165])).
% 3.38/3.55  cnf(c_0_174, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(X1,esk1_1(k1_zfmisc_1(esk6_0)))|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166, c_0_87]), c_0_66])).
% 3.38/3.55  cnf(c_0_175, negated_conjecture, (r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(k1_xboole_0))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_88, c_0_167])).
% 3.38/3.55  cnf(c_0_176, negated_conjecture, (r1_tarski(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)),k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_168, c_0_140])).
% 3.38/3.55  cnf(c_0_177, negated_conjecture, (esk2_2(k1_zfmisc_1(esk6_0),X1)=esk6_0|r1_tarski(k1_zfmisc_1(esk6_0),X1)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_169, c_0_74])).
% 3.38/3.55  cnf(c_0_178, negated_conjecture, (X1=esk6_0|~r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_170, c_0_171]), c_0_106])).
% 3.38/3.55  cnf(c_0_179, negated_conjecture, (v1_xboole_0(esk4_0)|~v1_xboole_0(esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_172, c_0_29]), c_0_58])]), c_0_59])).
% 3.38/3.55  cnf(c_0_180, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_173]), c_0_58]), c_0_29])])).
% 3.38/3.55  fof(c_0_181, plain, ![X42, X43]:(~v1_funct_1(X43)|~v1_funct_2(X43,X42,X42)|~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X42,X42)))|r2_hidden(X43,k1_funct_2(X42,X42))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).
% 3.38/3.55  cnf(c_0_182, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(X1,esk1_1(k1_zfmisc_1(X2)))|~v1_xboole_0(esk5_0)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_174, c_0_144])).
% 3.38/3.55  cnf(c_0_183, negated_conjecture, (r1_tarski(k5_partfun1(esk4_0,esk5_0,esk6_0),k1_zfmisc_1(X1))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_94, c_0_175])).
% 3.38/3.55  cnf(c_0_184, negated_conjecture, (r1_tarski(X1,k5_partfun1(esk4_0,esk5_0,esk6_0))|~r1_tarski(X1,k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_39, c_0_176])).
% 3.38/3.55  cnf(c_0_185, negated_conjecture, (~r1_tarski(k1_zfmisc_1(esk6_0),k1_funct_2(esk4_0,esk5_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_133])).
% 3.38/3.55  cnf(c_0_186, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk6_0),X1)|~r2_hidden(esk6_0,X1)|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_32, c_0_177])).
% 3.38/3.55  cnf(c_0_187, negated_conjecture, (esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))))=esk6_0|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_178, c_0_163])).
% 3.38/3.55  cnf(c_0_188, negated_conjecture, (v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_179, c_0_180]), c_0_49])])).
% 3.38/3.55  cnf(c_0_189, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_181])).
% 3.38/3.55  cnf(c_0_190, negated_conjecture, (v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(esk4_0,esk5_0))|~v1_xboole_0(esk5_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_182, c_0_171]), c_0_106])).
% 3.38/3.55  cnf(c_0_191, negated_conjecture, (k1_zfmisc_1(X1)=k5_partfun1(esk4_0,esk5_0,esk6_0)|~r1_tarski(k1_zfmisc_1(X1),k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_37, c_0_183])).
% 3.38/3.55  cnf(c_0_192, negated_conjecture, (r1_tarski(k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0)))),k5_partfun1(esk4_0,esk5_0,esk6_0))|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_184, c_0_159])).
% 3.38/3.55  cnf(c_0_193, negated_conjecture, (~r2_hidden(esk6_0,k1_funct_2(esk4_0,esk5_0))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_185, c_0_186])).
% 3.38/3.55  cnf(c_0_194, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_187, c_0_180]), c_0_48]), c_0_121]), c_0_121]), c_0_180]), c_0_49])])).
% 3.38/3.55  cnf(c_0_195, negated_conjecture, (esk4_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_75, c_0_188])).
% 3.38/3.55  cnf(c_0_196, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_2(X1,X2,X2)|~v1_funct_1(X1)|~r1_tarski(X1,k2_zfmisc_1(X2,X2))), inference(spm,[status(thm)],[c_0_189, c_0_42])).
% 3.38/3.55  cnf(c_0_197, negated_conjecture, (v1_funct_1(esk1_1(k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))))|~v1_xboole_0(esk5_0)), inference(spm,[status(thm)],[c_0_190, c_0_163])).
% 3.38/3.55  cnf(c_0_198, negated_conjecture, (k1_zfmisc_1(esk1_1(k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk5_0))))=k5_partfun1(esk4_0,esk5_0,esk6_0)|~v1_xboole_0(k2_zfmisc_1(esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_191, c_0_192])).
% 3.38/3.55  cnf(c_0_199, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.38/3.55  cnf(c_0_200, negated_conjecture, (~r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_193, c_0_180]), c_0_180]), c_0_49])]), c_0_194]), c_0_195])).
% 3.38/3.55  cnf(c_0_201, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_2(X1,X2,X2)|~v1_funct_1(X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_196, c_0_38])).
% 3.38/3.55  cnf(c_0_202, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_197, c_0_180]), c_0_48]), c_0_121]), c_0_121]), c_0_180]), c_0_49])])).
% 3.38/3.55  cnf(c_0_203, plain, (v1_funct_2(esk1_1(k5_partfun1(X1,X2,X3)),X1,X2)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_142, c_0_56])).
% 3.38/3.55  cnf(c_0_204, negated_conjecture, (k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_zfmisc_1(k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_198, c_0_180]), c_0_48]), c_0_121]), c_0_180]), c_0_180]), c_0_48]), c_0_49])]), c_0_195]), c_0_194])).
% 3.38/3.55  cnf(c_0_205, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_199])).
% 3.38/3.55  cnf(c_0_206, negated_conjecture, (~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_200, c_0_201]), c_0_202]), c_0_49])])).
% 3.38/3.55  cnf(c_0_207, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203, c_0_204]), c_0_121]), c_0_202]), c_0_205]), c_0_69])]), c_0_206]), c_0_47]), ['proof']).
% 3.38/3.55  # SZS output end CNFRefutation
% 3.38/3.55  # Proof object total steps             : 208
% 3.38/3.55  # Proof object clause steps            : 174
% 3.38/3.55  # Proof object formula steps           : 34
% 3.38/3.55  # Proof object conjectures             : 91
% 3.38/3.55  # Proof object clause conjectures      : 88
% 3.38/3.55  # Proof object formula conjectures     : 3
% 3.38/3.55  # Proof object initial clauses used    : 28
% 3.38/3.55  # Proof object initial formulas used   : 17
% 3.38/3.55  # Proof object generating inferences   : 137
% 3.38/3.55  # Proof object simplifying inferences  : 82
% 3.38/3.55  # Training examples: 0 positive, 0 negative
% 3.38/3.55  # Parsed axioms                        : 18
% 3.38/3.55  # Removed by relevancy pruning/SinE    : 0
% 3.38/3.55  # Initial clauses                      : 34
% 3.38/3.55  # Removed in clause preprocessing      : 0
% 3.38/3.55  # Initial clauses in saturation        : 34
% 3.38/3.55  # Processed clauses                    : 36262
% 3.38/3.55  # ...of these trivial                  : 66
% 3.38/3.55  # ...subsumed                          : 32944
% 3.38/3.55  # ...remaining for further processing  : 3252
% 3.38/3.55  # Other redundant clauses eliminated   : 5
% 3.38/3.55  # Clauses deleted for lack of memory   : 0
% 3.38/3.55  # Backward-subsumed                    : 469
% 3.38/3.55  # Backward-rewritten                   : 1850
% 3.38/3.55  # Generated clauses                    : 295361
% 3.38/3.55  # ...of the previous two non-trivial   : 275958
% 3.38/3.55  # Contextual simplify-reflections      : 472
% 3.38/3.55  # Paramodulations                      : 295356
% 3.38/3.55  # Factorizations                       : 0
% 3.38/3.55  # Equation resolutions                 : 5
% 3.38/3.55  # Propositional unsat checks           : 0
% 3.38/3.55  #    Propositional check models        : 0
% 3.38/3.55  #    Propositional check unsatisfiable : 0
% 3.38/3.55  #    Propositional clauses             : 0
% 3.38/3.55  #    Propositional clauses after purity: 0
% 3.38/3.55  #    Propositional unsat core size     : 0
% 3.38/3.55  #    Propositional preprocessing time  : 0.000
% 3.38/3.55  #    Propositional encoding time       : 0.000
% 3.38/3.55  #    Propositional solver time         : 0.000
% 3.38/3.55  #    Success case prop preproc time    : 0.000
% 3.38/3.55  #    Success case prop encoding time   : 0.000
% 3.38/3.55  #    Success case prop solver time     : 0.000
% 3.38/3.55  # Current number of processed clauses  : 928
% 3.38/3.55  #    Positive orientable unit clauses  : 30
% 3.38/3.55  #    Positive unorientable unit clauses: 0
% 3.38/3.55  #    Negative unit clauses             : 7
% 3.38/3.55  #    Non-unit-clauses                  : 891
% 3.38/3.55  # Current number of unprocessed clauses: 238152
% 3.38/3.55  # ...number of literals in the above   : 1343360
% 3.38/3.55  # Current number of archived formulas  : 0
% 3.38/3.55  # Current number of archived clauses   : 2319
% 3.38/3.55  # Clause-clause subsumption calls (NU) : 2004651
% 3.38/3.55  # Rec. Clause-clause subsumption calls : 857609
% 3.38/3.55  # Non-unit clause-clause subsumptions  : 29910
% 3.38/3.55  # Unit Clause-clause subsumption calls : 11022
% 3.38/3.55  # Rewrite failures with RHS unbound    : 0
% 3.38/3.55  # BW rewrite match attempts            : 191
% 3.38/3.55  # BW rewrite match successes           : 14
% 3.38/3.55  # Condensation attempts                : 0
% 3.38/3.55  # Condensation successes               : 0
% 3.38/3.55  # Termbank termtop insertions          : 5625151
% 3.38/3.56  
% 3.38/3.56  # -------------------------------------------------
% 3.38/3.56  # User time                : 3.101 s
% 3.38/3.56  # System time              : 0.108 s
% 3.38/3.56  # Total time               : 3.209 s
% 3.38/3.56  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
