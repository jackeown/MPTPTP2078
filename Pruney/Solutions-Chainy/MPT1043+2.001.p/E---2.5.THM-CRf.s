%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:08 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   84 (6606 expanded)
%              Number of clauses        :   56 (2600 expanded)
%              Number of leaves         :   14 (1650 expanded)
%              Depth                    :   18
%              Number of atoms          :  229 (23271 expanded)
%              Number of equality atoms :   42 (1612 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_2)).

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

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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
    ! [X56,X57,X58,X59] :
      ( ( v1_funct_1(X59)
        | ~ r2_hidden(X59,k5_partfun1(X56,X57,X58))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( v1_funct_2(X59,X56,X57)
        | ~ r2_hidden(X59,k5_partfun1(X56,X57,X58))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) )
      & ( m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))
        | ~ r2_hidden(X59,k5_partfun1(X56,X57,X58))
        | ~ v1_funct_1(X58)
        | ~ m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_16,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & ~ r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

cnf(c_0_17,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
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
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_23,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_24,plain,(
    ! [X51,X52,X53] :
      ( ( X52 = k1_xboole_0
        | r2_hidden(X53,k1_funct_2(X51,X52))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) )
      & ( X51 != k1_xboole_0
        | r2_hidden(X53,k1_funct_2(X51,X52))
        | ~ v1_funct_1(X53)
        | ~ v1_funct_2(X53,X51,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_25,negated_conjecture,
    ( v1_funct_2(X1,esk3_0,esk4_0)
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_18]),c_0_19])])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_18]),c_0_19])])).

fof(c_0_29,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_2(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),esk3_0,esk4_0)
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( v1_funct_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

fof(c_0_35,plain,(
    ! [X19,X20] :
      ( ( k2_zfmisc_1(X19,X20) != k1_xboole_0
        | X19 = k1_xboole_0
        | X20 = k1_xboole_0 )
      & ( X19 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X19,X20) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_36,plain,(
    ! [X48,X49,X50] :
      ( v1_xboole_0(X48)
      | ~ v1_xboole_0(X49)
      | ~ v1_funct_1(X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | v1_xboole_0(k5_partfun1(X48,X49,X50)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

cnf(c_0_37,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,negated_conjecture,
    ( r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_18])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | r2_hidden(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_funct_2(esk3_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_42,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X18] : r1_tarski(k1_xboole_0,X18) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,negated_conjecture,
    ( k2_zfmisc_1(esk3_0,esk4_0) = esk5_0
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_46,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_50,plain,(
    ! [X15] :
      ( ~ v1_xboole_0(X15)
      | X15 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))
    | v1_xboole_0(esk3_0)
    | ~ v1_xboole_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_18]),c_0_19])])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_46]),c_0_47]),c_0_46]),c_0_47]),c_0_48])])).

cnf(c_0_54,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0))
    | v1_xboole_0(esk3_0) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_46]),c_0_46]),c_0_52])]),c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk3_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_46]),c_0_46]),c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk4_0))
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_57])).

cnf(c_0_61,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_48])])).

cnf(c_0_62,plain,
    ( v1_funct_2(X1,X2,k1_xboole_0)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
    | ~ r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X3)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_47])).

cnf(c_0_63,negated_conjecture,
    ( esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)) = k2_zfmisc_1(esk3_0,esk4_0)
    | v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_61])).

fof(c_0_65,plain,(
    ! [X21] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k2_zfmisc_1(esk3_0,esk4_0))
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_33])).

cnf(c_0_67,plain,
    ( v1_funct_2(esk1_1(k5_partfun1(X1,k1_xboole_0,X2)),X1,k1_xboole_0)
    | v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X2))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_54])).

cnf(c_0_68,negated_conjecture,
    ( esk1_1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_46]),c_0_46]),c_0_47]),c_0_46]),c_0_46]),c_0_47]),c_0_46]),c_0_48])]),c_0_64]),c_0_53]),c_0_64]),c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_19,c_0_53])).

cnf(c_0_70,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_71,negated_conjecture,
    ( esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1) = k2_zfmisc_1(esk3_0,esk4_0)
    | r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)
    | ~ r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_66])).

fof(c_0_72,plain,(
    ! [X54,X55] :
      ( ~ v1_funct_1(X55)
      | ~ v1_funct_2(X55,X54,X54)
      | ~ m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X54)))
      | r2_hidden(X55,k1_funct_2(X54,X54)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).

cnf(c_0_73,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69]),c_0_70])])).

cnf(c_0_74,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_75,negated_conjecture,
    ( esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) = k1_xboole_0
    | r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_46]),c_0_46]),c_0_47]),c_0_46]),c_0_46]),c_0_47]),c_0_46]),c_0_48])]),c_0_64]),c_0_53]),c_0_64]),c_0_53])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_73])).

cnf(c_0_78,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_75])).

cnf(c_0_80,negated_conjecture,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_69]),c_0_78]),c_0_70])])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_64]),c_0_64])).

cnf(c_0_82,negated_conjecture,
    ( k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82]),c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.20/0.50  # and selection function PSelectComplexPreferEQ.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.029 s
% 0.20/0.50  # Presaturation interreduction done
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_funct_2)).
% 0.20/0.50  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_2)).
% 0.20/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.50  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_funct_2)).
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.50  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.20/0.50  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.50  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.20/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 0.20/0.50  fof(t12_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>r2_hidden(X2,k1_funct_2(X1,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_2)).
% 0.20/0.50  fof(c_0_14, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.20/0.50  fof(c_0_15, plain, ![X56, X57, X58, X59]:(((v1_funct_1(X59)|~r2_hidden(X59,k5_partfun1(X56,X57,X58))|(~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))&(v1_funct_2(X59,X56,X57)|~r2_hidden(X59,k5_partfun1(X56,X57,X58))|(~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57))))))&(m1_subset_1(X59,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))|~r2_hidden(X59,k5_partfun1(X56,X57,X58))|(~v1_funct_1(X58)|~m1_subset_1(X58,k1_zfmisc_1(k2_zfmisc_1(X56,X57)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.20/0.50  fof(c_0_16, negated_conjecture, ((v1_funct_1(esk5_0)&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&~r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.20/0.50  cnf(c_0_17, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  fof(c_0_20, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.50  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_22, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  fof(c_0_23, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.50  fof(c_0_24, plain, ![X51, X52, X53]:((X52=k1_xboole_0|r2_hidden(X53,k1_funct_2(X51,X52))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))&(X51!=k1_xboole_0|r2_hidden(X53,k1_funct_2(X51,X52))|(~v1_funct_1(X53)|~v1_funct_2(X53,X51,X52)|~m1_subset_1(X53,k1_zfmisc_1(k2_zfmisc_1(X51,X52)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.20/0.50  cnf(c_0_25, negated_conjecture, (v1_funct_2(X1,esk3_0,esk4_0)|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.20/0.50  cnf(c_0_26, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_27, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_18]), c_0_19])])).
% 0.20/0.50  cnf(c_0_28, negated_conjecture, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_18]), c_0_19])])).
% 0.20/0.50  fof(c_0_29, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  cnf(c_0_30, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.50  cnf(c_0_31, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.50  cnf(c_0_32, negated_conjecture, (v1_funct_2(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),esk3_0,esk4_0)|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.50  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_27, c_0_26])).
% 0.20/0.50  cnf(c_0_34, negated_conjecture, (v1_funct_1(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_28, c_0_26])).
% 0.20/0.50  fof(c_0_35, plain, ![X19, X20]:((k2_zfmisc_1(X19,X20)!=k1_xboole_0|(X19=k1_xboole_0|X20=k1_xboole_0))&((X19!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0)&(X20!=k1_xboole_0|k2_zfmisc_1(X19,X20)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.50  fof(c_0_36, plain, ![X48, X49, X50]:(v1_xboole_0(X48)|~v1_xboole_0(X49)|~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|v1_xboole_0(k5_partfun1(X48,X49,X50))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.20/0.50  cnf(c_0_37, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.20/0.50  cnf(c_0_38, negated_conjecture, (r1_tarski(esk5_0,k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_30, c_0_18])).
% 0.20/0.50  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.50  cnf(c_0_40, negated_conjecture, (esk4_0=k1_xboole_0|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|r2_hidden(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k1_funct_2(esk3_0,esk4_0))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33]), c_0_34])).
% 0.20/0.50  cnf(c_0_41, negated_conjecture, (~r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),k1_funct_2(esk3_0,esk4_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_42, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.50  fof(c_0_43, plain, ![X18]:r1_tarski(k1_xboole_0,X18), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.50  cnf(c_0_44, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.50  cnf(c_0_45, negated_conjecture, (k2_zfmisc_1(esk3_0,esk4_0)=esk5_0|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.50  cnf(c_0_46, negated_conjecture, (esk4_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41])).
% 0.20/0.50  cnf(c_0_47, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_42])).
% 0.20/0.50  cnf(c_0_48, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.50  fof(c_0_49, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.50  fof(c_0_50, plain, ![X15]:(~v1_xboole_0(X15)|X15=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.50  cnf(c_0_51, negated_conjecture, (v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))|v1_xboole_0(esk3_0)|~v1_xboole_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_18]), c_0_19])])).
% 0.20/0.50  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.20/0.50  cnf(c_0_53, negated_conjecture, (esk5_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_46]), c_0_47]), c_0_46]), c_0_47]), c_0_48])])).
% 0.20/0.50  cnf(c_0_54, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.50  cnf(c_0_55, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.50  cnf(c_0_56, negated_conjecture, (v1_xboole_0(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0))|v1_xboole_0(esk3_0)), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_46]), c_0_46]), c_0_52])]), c_0_53])).
% 0.20/0.50  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_27, c_0_54])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (~r1_tarski(k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0),k1_funct_2(esk3_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_41, c_0_46]), c_0_46]), c_0_53])).
% 0.20/0.50  cnf(c_0_59, negated_conjecture, (k5_partfun1(esk3_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (r1_tarski(esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)),k2_zfmisc_1(esk3_0,esk4_0))|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_57])).
% 0.20/0.50  cnf(c_0_61, negated_conjecture, (v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_48])])).
% 0.20/0.50  cnf(c_0_62, plain, (v1_funct_2(X1,X2,k1_xboole_0)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))|~r2_hidden(X1,k5_partfun1(X2,k1_xboole_0,X3))), inference(spm,[status(thm)],[c_0_17, c_0_47])).
% 0.20/0.50  cnf(c_0_63, negated_conjecture, (esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0))=k2_zfmisc_1(esk3_0,esk4_0)|v1_xboole_0(k5_partfun1(esk3_0,esk4_0,esk5_0))|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk1_1(k5_partfun1(esk3_0,esk4_0,esk5_0)))), inference(spm,[status(thm)],[c_0_37, c_0_60])).
% 0.20/0.50  cnf(c_0_64, negated_conjecture, (esk3_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_55, c_0_61])).
% 0.20/0.50  fof(c_0_65, plain, ![X21]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X21)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.20/0.50  cnf(c_0_66, negated_conjecture, (r1_tarski(esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1),k2_zfmisc_1(esk3_0,esk4_0))|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)), inference(spm,[status(thm)],[c_0_30, c_0_33])).
% 0.20/0.50  cnf(c_0_67, plain, (v1_funct_2(esk1_1(k5_partfun1(X1,k1_xboole_0,X2)),X1,k1_xboole_0)|v1_xboole_0(k5_partfun1(X1,k1_xboole_0,X2))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_62, c_0_54])).
% 0.20/0.50  cnf(c_0_68, negated_conjecture, (esk1_1(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))=k1_xboole_0|v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_46]), c_0_46]), c_0_47]), c_0_46]), c_0_46]), c_0_47]), c_0_46]), c_0_48])]), c_0_64]), c_0_53]), c_0_64]), c_0_53])).
% 0.20/0.50  cnf(c_0_69, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_19, c_0_53])).
% 0.20/0.50  cnf(c_0_70, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_65])).
% 0.20/0.50  cnf(c_0_71, negated_conjecture, (esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)=k2_zfmisc_1(esk3_0,esk4_0)|r1_tarski(k5_partfun1(esk3_0,esk4_0,esk5_0),X1)|~r1_tarski(k2_zfmisc_1(esk3_0,esk4_0),esk2_2(k5_partfun1(esk3_0,esk4_0,esk5_0),X1))), inference(spm,[status(thm)],[c_0_37, c_0_66])).
% 0.20/0.50  fof(c_0_72, plain, ![X54, X55]:(~v1_funct_1(X55)|~v1_funct_2(X55,X54,X54)|~m1_subset_1(X55,k1_zfmisc_1(k2_zfmisc_1(X54,X54)))|r2_hidden(X55,k1_funct_2(X54,X54))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).
% 0.20/0.50  cnf(c_0_73, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)|v1_xboole_0(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69]), c_0_70])])).
% 0.20/0.50  cnf(c_0_74, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (esk2_2(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)=k1_xboole_0|r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_71, c_0_46]), c_0_46]), c_0_47]), c_0_46]), c_0_46]), c_0_47]), c_0_46]), c_0_48])]), c_0_64]), c_0_53]), c_0_64]), c_0_53])).
% 0.20/0.50  cnf(c_0_76, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.20/0.50  cnf(c_0_77, negated_conjecture, (k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_55, c_0_73])).
% 0.20/0.50  cnf(c_0_78, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_74])).
% 0.20/0.50  cnf(c_0_79, negated_conjecture, (r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),X1)|~r2_hidden(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_39, c_0_75])).
% 0.20/0.50  cnf(c_0_80, negated_conjecture, (k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0|r2_hidden(k1_xboole_0,k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_69]), c_0_78]), c_0_70])])).
% 0.20/0.50  cnf(c_0_81, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_64]), c_0_64])).
% 0.20/0.50  cnf(c_0_82, negated_conjecture, (k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_81])).
% 0.20/0.50  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82]), c_0_48])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 84
% 0.20/0.50  # Proof object clause steps            : 56
% 0.20/0.50  # Proof object formula steps           : 28
% 0.20/0.50  # Proof object conjectures             : 38
% 0.20/0.50  # Proof object clause conjectures      : 35
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 20
% 0.20/0.50  # Proof object initial formulas used   : 14
% 0.20/0.50  # Proof object generating inferences   : 26
% 0.20/0.50  # Proof object simplifying inferences  : 69
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 23
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 38
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 38
% 0.20/0.50  # Processed clauses                    : 1740
% 0.20/0.50  # ...of these trivial                  : 42
% 0.20/0.50  # ...subsumed                          : 1044
% 0.20/0.50  # ...remaining for further processing  : 654
% 0.20/0.50  # Other redundant clauses eliminated   : 7
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 24
% 0.20/0.50  # Backward-rewritten                   : 282
% 0.20/0.50  # Generated clauses                    : 4826
% 0.20/0.50  # ...of the previous two non-trivial   : 4171
% 0.20/0.50  # Contextual simplify-reflections      : 17
% 0.20/0.50  # Paramodulations                      : 4809
% 0.20/0.50  # Factorizations                       : 10
% 0.20/0.50  # Equation resolutions                 : 7
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 306
% 0.20/0.50  #    Positive orientable unit clauses  : 28
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 4
% 0.20/0.50  #    Non-unit-clauses                  : 274
% 0.20/0.50  # Current number of unprocessed clauses: 2456
% 0.20/0.50  # ...number of literals in the above   : 8036
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 343
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 24875
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 17419
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 910
% 0.20/0.50  # Unit Clause-clause subsumption calls : 715
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 44
% 0.20/0.50  # BW rewrite match successes           : 7
% 0.20/0.50  # Condensation attempts                : 0
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 75730
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.145 s
% 0.20/0.50  # System time              : 0.010 s
% 0.20/0.50  # Total time               : 0.155 s
% 0.20/0.50  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
