%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:09 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   95 (6771 expanded)
%              Number of clauses        :   67 (2702 expanded)
%              Number of leaves         :   14 (1689 expanded)
%              Depth                    :   19
%              Number of atoms          :  254 (23884 expanded)
%              Number of equality atoms :   37 (1544 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

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

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_funct_2)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_partfun1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t12_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => r2_hidden(X2,k1_funct_2(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_2)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

fof(c_0_15,plain,(
    ! [X21,X22,X23] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(X21))
      | ~ r2_hidden(X23,X22)
      | r2_hidden(X23,X21) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & ~ r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_17,plain,(
    ! [X36,X37,X38,X39] :
      ( ( v1_funct_1(X39)
        | ~ r2_hidden(X39,k5_partfun1(X36,X37,X38))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v1_funct_2(X39,X36,X37)
        | ~ r2_hidden(X39,k5_partfun1(X36,X37,X38))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))
        | ~ r2_hidden(X39,k5_partfun1(X36,X37,X38))
        | ~ v1_funct_1(X38)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_20,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_21,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_27,plain,(
    ! [X31,X32,X33] :
      ( ( X32 = k1_xboole_0
        | r2_hidden(X33,k1_funct_2(X31,X32))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) )
      & ( X31 != k1_xboole_0
        | r2_hidden(X33,k1_funct_2(X31,X32))
        | ~ v1_funct_1(X33)
        | ~ v1_funct_2(X33,X31,X32)
        | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_2(X1,esk3_0,esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_19]),c_0_22])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_19]),c_0_22])])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_19]),c_0_22])])).

fof(c_0_31,plain,(
    ! [X15,X16] :
      ( ( r1_tarski(X15,X16)
        | X15 != X16 )
      & ( r1_tarski(X16,X15)
        | X15 != X16 )
      & ( ~ r1_tarski(X15,X16)
        | ~ r1_tarski(X16,X15)
        | X15 = X16 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | r2_hidden(esk2_2(esk5_0,X1),k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_2(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),esk3_0,esk4_0)
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_26])).

cnf(c_0_37,negated_conjecture,
    ( v1_funct_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

fof(c_0_38,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_39,plain,(
    ! [X28,X29,X30] :
      ( v1_xboole_0(X28)
      | ~ v1_xboole_0(X29)
      | ~ v1_funct_1(X30)
      | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | v1_xboole_0(k5_partfun1(X28,X29,X30)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

cnf(c_0_40,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | r2_hidden(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_funct_2(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37])).

cnf(c_0_43,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_45,plain,(
    ! [X17] : r1_tarski(k1_xboole_0,X17) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_46,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_42]),c_0_43])).

cnf(c_0_50,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_53,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_19]),c_0_22])])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49]),c_0_50]),c_0_49]),c_0_50]),c_0_51])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_52])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_26])).

cnf(c_0_59,negated_conjecture,
    ( v1_xboole_0(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_49]),c_0_49]),c_0_55])]),c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))
    | ~ r2_hidden(X1,esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk3_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_49]),c_0_49]),c_0_56])).

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),X1)
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | r2_hidden(X2,k2_zfmisc_1(esk3_0,esk4_0))
    | ~ r2_hidden(X2,esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_36])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),X1)
    | r2_hidden(esk2_2(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),X1),k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_26])).

fof(c_0_65,plain,(
    ! [X18] :
      ( ~ r1_tarski(X18,k1_xboole_0)
      | X18 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | r2_hidden(esk1_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)),k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_63,c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_64])).

cnf(c_0_69,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | v1_xboole_0(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_67])).

cnf(c_0_72,plain,
    ( v1_funct_2(X1,X2,k1_xboole_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_50])).

cnf(c_0_73,negated_conjecture,
    ( esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)) = k2_zfmisc_1(esk3_0,esk4_0)
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_75,plain,(
    ! [X24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),X1)
    | v1_xboole_0(esk2_2(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_49]),c_0_49]),c_0_49]),c_0_50]),c_0_55])]),c_0_56]),c_0_56])).

cnf(c_0_77,plain,
    ( v1_funct_2(esk1_1(k5_partfun1(X1,k1_xboole_0,X2)),X1,k1_xboole_0)
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_52])).

cnf(c_0_78,negated_conjecture,
    ( esk1_1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_49]),c_0_49]),c_0_50]),c_0_49]),c_0_49]),c_0_50]),c_0_49]),c_0_51])]),c_0_74]),c_0_56]),c_0_74]),c_0_56])).

cnf(c_0_79,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_22,c_0_56])).

cnf(c_0_80,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)
    | v1_xboole_0(esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_74]),c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79]),c_0_80])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1),X2)
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_81])).

fof(c_0_84,plain,(
    ! [X34,X35] :
      ( ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,X34,X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X34)))
      | r2_hidden(X35,k1_funct_2(X34,X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).

cnf(c_0_85,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_74]),c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_82])).

cnf(c_0_87,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_88,negated_conjecture,
    ( esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(spm,[status(thm)],[c_0_69,c_0_83])).

cnf(c_0_89,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_85,c_0_86])).

cnf(c_0_91,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_87])).

cnf(c_0_92,negated_conjecture,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_79]),c_0_91]),c_0_80])])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.13/0.40  # and selection function PSelectComplexPreferEQ.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.028 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 0.13/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.13/0.40  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.13/0.40  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.40  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.13/0.40  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.13/0.40  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.40  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.13/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.40  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.13/0.40  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.40  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.40  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.13/0.40  fof(t12_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>r2_hidden(X2,k1_funct_2(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_2)).
% 0.13/0.40  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.13/0.40  fof(c_0_15, plain, ![X21, X22, X23]:(~m1_subset_1(X22,k1_zfmisc_1(X21))|(~r2_hidden(X23,X22)|r2_hidden(X23,X21))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.13/0.40  fof(c_0_16, negated_conjecture, ((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&~r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.13/0.40  fof(c_0_17, plain, ![X36, X37, X38, X39]:(((v1_funct_1(X39)|~r2_hidden(X39,k5_partfun1(X36,X37,X38))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))&(v1_funct_2(X39,X36,X37)|~r2_hidden(X39,k5_partfun1(X36,X37,X38))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))))&(m1_subset_1(X39,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))|~r2_hidden(X39,k5_partfun1(X36,X37,X38))|(~v1_funct_1(X38)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.13/0.40  cnf(c_0_18, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.40  cnf(c_0_19, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  fof(c_0_20, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.40  cnf(c_0_21, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_24, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  fof(c_0_27, plain, ![X31, X32, X33]:((X32=k1_xboole_0|r2_hidden(X33,k1_funct_2(X31,X32))|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))&(X31!=k1_xboole_0|r2_hidden(X33,k1_funct_2(X31,X32))|(~v1_funct_1(X33)|~v1_funct_2(X33,X31,X32)|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(X31,X32)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (v1_funct_2(X1,esk3_0,esk4_0)|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_19]), c_0_22])])).
% 0.13/0.40  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_19]), c_0_22])])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_19]), c_0_22])])).
% 0.13/0.40  fof(c_0_31, plain, ![X15, X16]:(((r1_tarski(X15,X16)|X15!=X16)&(r1_tarski(X16,X15)|X15!=X16))&(~r1_tarski(X15,X16)|~r1_tarski(X16,X15)|X15=X16)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.13/0.40  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (r1_tarski(esk5_0,X1)|r2_hidden(esk2_2(esk5_0,X1),k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.13/0.40  cnf(c_0_34, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (v1_funct_2(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),esk3_0,esk4_0)|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_29, c_0_26])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (v1_funct_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_26])).
% 0.13/0.40  fof(c_0_38, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.40  fof(c_0_39, plain, ![X28, X29, X30]:(v1_xboole_0(X28)|~v1_xboole_0(X29)|~v1_funct_1(X30)|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|v1_xboole_0(k5_partfun1(X28,X29,X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.13/0.40  cnf(c_0_40, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|r2_hidden(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_funct_2(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (~r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.40  cnf(c_0_44, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  fof(c_0_45, plain, ![X17]:r1_tarski(k1_xboole_0,X17), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.40  fof(c_0_46, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.13/0.40  cnf(c_0_47, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.13/0.40  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=esk5_0|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.40  cnf(c_0_49, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_42]), c_0_43])).
% 0.13/0.40  cnf(c_0_50, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_44])).
% 0.13/0.40  cnf(c_0_51, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.13/0.40  cnf(c_0_52, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_53, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))|v1_xboole_0(esk3_0)|~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_19]), c_0_22])])).
% 0.13/0.40  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.40  cnf(c_0_56, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49]), c_0_50]), c_0_49]), c_0_50]), c_0_51])])).
% 0.13/0.40  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_29, c_0_52])).
% 0.13/0.40  cnf(c_0_58, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_53, c_0_26])).
% 0.13/0.40  cnf(c_0_59, negated_conjecture, (v1_xboole_0(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0))|v1_xboole_0(esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_49]), c_0_49]), c_0_55])]), c_0_56])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))|~r2_hidden(X1,esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_18, c_0_57])).
% 0.13/0.40  cnf(c_0_61, negated_conjecture, (~r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk3_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_49]), c_0_49]), c_0_56])).
% 0.13/0.40  cnf(c_0_62, negated_conjecture, (r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),X1)|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.13/0.40  cnf(c_0_63, negated_conjecture, (r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|r2_hidden(X2,k2_zfmisc_1(esk3_0,esk4_0))|~r2_hidden(X2,esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))), inference(spm,[status(thm)],[c_0_18, c_0_36])).
% 0.13/0.40  cnf(c_0_64, negated_conjecture, (r1_tarski(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),X1)|r2_hidden(esk2_2(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),X1),k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_60, c_0_26])).
% 0.13/0.40  fof(c_0_65, plain, ![X18]:(~r1_tarski(X18,k1_xboole_0)|X18=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.13/0.40  cnf(c_0_67, negated_conjecture, (r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|r2_hidden(esk1_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)),k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))), inference(spm,[status(thm)],[c_0_63, c_0_52])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (r1_tarski(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_32, c_0_64])).
% 0.13/0.40  cnf(c_0_69, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.13/0.40  cnf(c_0_70, negated_conjecture, (r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_58, c_0_66])).
% 0.13/0.40  cnf(c_0_71, negated_conjecture, (r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|v1_xboole_0(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_67])).
% 0.13/0.40  cnf(c_0_72, plain, (v1_funct_2(X1,X2,k1_xboole_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_21, c_0_50])).
% 0.13/0.40  cnf(c_0_73, negated_conjecture, (esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0))=k2_zfmisc_1(esk3_0,esk4_0)|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_40, c_0_68])).
% 0.13/0.40  cnf(c_0_74, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_69, c_0_70])).
% 0.13/0.40  fof(c_0_75, plain, ![X24]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X24)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),X1)|v1_xboole_0(esk2_2(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_49]), c_0_49]), c_0_49]), c_0_50]), c_0_55])]), c_0_56]), c_0_56])).
% 0.13/0.40  cnf(c_0_77, plain, (v1_funct_2(esk1_1(k5_partfun1(X1,k1_xboole_0,X2)),X1,k1_xboole_0)|v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X2))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_72, c_0_52])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (esk1_1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))=k1_xboole_0|v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_49]), c_0_49]), c_0_50]), c_0_49]), c_0_49]), c_0_50]), c_0_49]), c_0_51])]), c_0_74]), c_0_56]), c_0_74]), c_0_56])).
% 0.13/0.40  cnf(c_0_79, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_22, c_0_56])).
% 0.13/0.40  cnf(c_0_80, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.13/0.40  cnf(c_0_81, negated_conjecture, (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)|v1_xboole_0(esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_74]), c_0_74])).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79]), c_0_80])])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (r1_tarski(esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1),X2)|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_58, c_0_81])).
% 0.13/0.40  fof(c_0_84, plain, ![X34, X35]:(~v1_funct_1(X35)|~v1_funct_2(X35,X34,X34)|~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(X34,X34)))|r2_hidden(X35,k1_funct_2(X34,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).
% 0.13/0.40  cnf(c_0_85, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_74]), c_0_74])).
% 0.13/0.40  cnf(c_0_86, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_58, c_0_82])).
% 0.13/0.40  cnf(c_0_87, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_88, negated_conjecture, (esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(spm,[status(thm)],[c_0_69, c_0_83])).
% 0.13/0.40  cnf(c_0_89, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_84])).
% 0.13/0.40  cnf(c_0_90, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_85, c_0_86])).
% 0.13/0.40  cnf(c_0_91, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_87])).
% 0.13/0.40  cnf(c_0_92, negated_conjecture, (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_32, c_0_88])).
% 0.13/0.40  cnf(c_0_93, negated_conjecture, (r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_90]), c_0_79]), c_0_91]), c_0_80])])).
% 0.13/0.40  cnf(c_0_94, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_93]), c_0_85]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 95
% 0.13/0.40  # Proof object clause steps            : 67
% 0.13/0.40  # Proof object formula steps           : 28
% 0.13/0.40  # Proof object conjectures             : 47
% 0.13/0.40  # Proof object clause conjectures      : 44
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 21
% 0.13/0.40  # Proof object initial formulas used   : 14
% 0.13/0.40  # Proof object generating inferences   : 36
% 0.13/0.40  # Proof object simplifying inferences  : 61
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 15
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 27
% 0.13/0.40  # Removed in clause preprocessing      : 0
% 0.13/0.40  # Initial clauses in saturation        : 27
% 0.13/0.40  # Processed clauses                    : 293
% 0.13/0.40  # ...of these trivial                  : 19
% 0.13/0.40  # ...subsumed                          : 58
% 0.13/0.40  # ...remaining for further processing  : 216
% 0.13/0.40  # Other redundant clauses eliminated   : 7
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 6
% 0.13/0.40  # Backward-rewritten                   : 88
% 0.13/0.40  # Generated clauses                    : 555
% 0.13/0.40  # ...of the previous two non-trivial   : 455
% 0.13/0.40  # Contextual simplify-reflections      : 11
% 0.13/0.40  # Paramodulations                      : 534
% 0.13/0.40  # Factorizations                       : 8
% 0.13/0.40  # Equation resolutions                 : 7
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 85
% 0.13/0.40  #    Positive orientable unit clauses  : 14
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 3
% 0.13/0.40  #    Non-unit-clauses                  : 68
% 0.13/0.40  # Current number of unprocessed clauses: 198
% 0.13/0.40  # ...number of literals in the above   : 754
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 126
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 2317
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1325
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 75
% 0.13/0.40  # Unit Clause-clause subsumption calls : 185
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 15
% 0.13/0.40  # BW rewrite match successes           : 8
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 13872
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.051 s
% 0.13/0.40  # System time              : 0.002 s
% 0.13/0.40  # Total time               : 0.053 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
