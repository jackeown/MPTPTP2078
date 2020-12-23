%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:07:09 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 697 expanded)
%              Number of clauses        :   60 ( 313 expanded)
%              Number of leaves         :   13 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 (2546 expanded)
%              Number of equality atoms :   35 ( 225 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t158_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ! [X4] :
          ( r2_hidden(X4,k5_partfun1(X1,X2,X3))
         => ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X2)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_2)).

fof(t159_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_2)).

fof(fc2_partfun1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & v1_xboole_0(X2)
        & v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => v1_xboole_0(k5_partfun1(X1,X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_partfun1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t11_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( X2 = k1_xboole_0
         => X1 = k1_xboole_0 )
       => r2_hidden(X3,k1_funct_2(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t12_funct_2,axiom,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => r2_hidden(X2,k1_funct_2(X1,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).

fof(c_0_13,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ( ~ m1_subset_1(X16,k1_zfmisc_1(X17))
        | r1_tarski(X16,X17) )
      & ( ~ r1_tarski(X16,X17)
        | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | ~ v1_xboole_0(X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_22,plain,(
    ! [X35,X36,X37,X38] :
      ( ( v1_funct_1(X38)
        | ~ r2_hidden(X38,k5_partfun1(X35,X36,X37))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( v1_funct_2(X38,X35,X36)
        | ~ r2_hidden(X38,k5_partfun1(X35,X36,X37))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) )
      & ( m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
        | ~ r2_hidden(X38,k5_partfun1(X35,X36,X37))
        | ~ v1_funct_1(X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)) ) ),
    inference(assume_negation,[status(cth)],[t159_funct_2])).

cnf(c_0_24,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_25,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_26,plain,(
    ! [X27,X28,X29] :
      ( v1_xboole_0(X27)
      | ~ v1_xboole_0(X28)
      | ~ v1_funct_1(X29)
      | ~ m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))
      | v1_xboole_0(k5_partfun1(X27,X28,X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).

fof(c_0_27,plain,(
    ! [X13,X14] :
      ( ( k2_zfmisc_1(X13,X14) != k1_xboole_0
        | X13 = k1_xboole_0
        | X14 = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 )
      & ( X14 != k1_xboole_0
        | k2_zfmisc_1(X13,X14) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_28,plain,(
    ! [X30,X31,X32] :
      ( ( X31 = k1_xboole_0
        | r2_hidden(X32,k1_funct_2(X30,X31))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) )
      & ( X30 != k1_xboole_0
        | r2_hidden(X32,k1_funct_2(X30,X31))
        | ~ v1_funct_1(X32)
        | ~ v1_funct_2(X32,X30,X31)
        | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).

cnf(c_0_29,plain,
    ( v1_funct_2(X1,X2,X3)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( v1_funct_1(X1)
    | ~ r2_hidden(X1,k5_partfun1(X2,X3,X4))
    | ~ v1_funct_1(X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_34,negated_conjecture,
    ( v1_funct_1(esk4_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & ~ r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

fof(c_0_35,plain,(
    ! [X15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X2,X3))
    | ~ v1_xboole_0(X2)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_38,plain,(
    ! [X24,X25,X26] :
      ( ~ v1_xboole_0(X24)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X24)))
      | v1_xboole_0(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,k1_funct_2(X3,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,plain,
    ( v1_funct_2(esk1_2(k5_partfun1(X1,X2,X3),X4),X1,X2)
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_42,plain,
    ( m1_subset_1(esk1_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_30,c_0_25])).

cnf(c_0_43,plain,
    ( v1_funct_1(esk1_2(k5_partfun1(X1,X2,X3),X4))
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_47,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | r1_tarski(k5_partfun1(X1,X2,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_51,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_53,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_54,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(k5_partfun1(X2,X1,X3),X4),k1_funct_2(X2,X1))
    | r1_tarski(k5_partfun1(X2,X1,X3),X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_45])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | r1_tarski(k5_partfun1(X2,X1,X3),k1_funct_2(X2,X1))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(esk2_0,esk3_0)),esk4_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_61,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_20])).

cnf(c_0_62,plain,
    ( r1_tarski(k1_xboole_0,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_56,c_0_25])).

cnf(c_0_63,negated_conjecture,
    ( v1_xboole_0(esk2_0)
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_64,negated_conjecture,
    ( esk3_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_59]),c_0_49]),c_0_45])])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_25])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_36,c_0_61])).

cnf(c_0_68,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_62,c_0_52])).

cnf(c_0_69,negated_conjecture,
    ( v1_xboole_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64]),c_0_46])])).

cnf(c_0_70,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,plain,
    ( r1_tarski(k2_zfmisc_1(X1,X2),X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_58])).

fof(c_0_72,plain,(
    ! [X33,X34] :
      ( ~ v1_funct_1(X34)
      | ~ v1_funct_2(X34,X33,X33)
      | ~ m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33)))
      | r2_hidden(X34,k1_funct_2(X33,X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).

cnf(c_0_73,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r1_tarski(esk2_0,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( k2_zfmisc_1(esk2_0,esk3_0) = esk4_0
    | ~ m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_76,plain,
    ( r2_hidden(X1,k1_funct_2(X2,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( esk2_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( esk4_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_64]),c_0_51]),c_0_64]),c_0_46])])).

cnf(c_0_79,plain,
    ( r2_hidden(esk1_2(k5_partfun1(X1,X1,X2),X3),k1_funct_2(X1,X1))
    | r1_tarski(k5_partfun1(X1,X1,X2),X3)
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_80,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_64]),c_0_64]),c_0_77]),c_0_78]),c_0_77])).

cnf(c_0_82,plain,
    ( r1_tarski(k5_partfun1(X1,X1,X2),k1_funct_2(X1,X1))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( v1_funct_1(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_49,c_0_78])).

cnf(c_0_84,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83]),c_0_84]),c_0_46])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:20:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.19/0.50  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.028 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.50  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.50  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.50  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.50  fof(t158_funct_2, axiom, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>![X4]:(r2_hidden(X4,k5_partfun1(X1,X2,X3))=>((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_2)).
% 0.19/0.50  fof(t159_funct_2, conjecture, ![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_funct_2)).
% 0.19/0.50  fof(fc2_partfun1, axiom, ![X1, X2, X3]:((((~(v1_xboole_0(X1))&v1_xboole_0(X2))&v1_funct_1(X3))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>v1_xboole_0(k5_partfun1(X1,X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_partfun1)).
% 0.19/0.50  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.50  fof(t11_funct_2, axiom, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((X2=k1_xboole_0=>X1=k1_xboole_0)=>r2_hidden(X3,k1_funct_2(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 0.19/0.50  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 0.19/0.50  fof(cc4_relset_1, axiom, ![X1, X2]:(v1_xboole_0(X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))=>v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 0.19/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.50  fof(t12_funct_2, axiom, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>r2_hidden(X2,k1_funct_2(X1,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_2)).
% 0.19/0.50  fof(c_0_13, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.50  fof(c_0_14, plain, ![X16, X17]:((~m1_subset_1(X16,k1_zfmisc_1(X17))|r1_tarski(X16,X17))&(~r1_tarski(X16,X17)|m1_subset_1(X16,k1_zfmisc_1(X17)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.50  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  fof(c_0_16, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|~v1_xboole_0(X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.50  cnf(c_0_17, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.50  cnf(c_0_18, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.50  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.50  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.50  fof(c_0_21, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.50  fof(c_0_22, plain, ![X35, X36, X37, X38]:(((v1_funct_1(X38)|~r2_hidden(X38,k5_partfun1(X35,X36,X37))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))&(v1_funct_2(X38,X35,X36)|~r2_hidden(X38,k5_partfun1(X35,X36,X37))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36))))))&(m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|~r2_hidden(X38,k5_partfun1(X35,X36,X37))|(~v1_funct_1(X37)|~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t158_funct_2])])])])).
% 0.19/0.50  fof(c_0_23, negated_conjecture, ~(![X1, X2, X3]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>r1_tarski(k5_partfun1(X1,X2,X3),k1_funct_2(X1,X2)))), inference(assume_negation,[status(cth)],[t159_funct_2])).
% 0.19/0.50  cnf(c_0_24, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.50  cnf(c_0_25, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  fof(c_0_26, plain, ![X27, X28, X29]:(v1_xboole_0(X27)|~v1_xboole_0(X28)|~v1_funct_1(X29)|~m1_subset_1(X29,k1_zfmisc_1(k2_zfmisc_1(X27,X28)))|v1_xboole_0(k5_partfun1(X27,X28,X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_partfun1])])])).
% 0.19/0.50  fof(c_0_27, plain, ![X13, X14]:((k2_zfmisc_1(X13,X14)!=k1_xboole_0|(X13=k1_xboole_0|X14=k1_xboole_0))&((X13!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0)&(X14!=k1_xboole_0|k2_zfmisc_1(X13,X14)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.50  fof(c_0_28, plain, ![X30, X31, X32]:((X31=k1_xboole_0|r2_hidden(X32,k1_funct_2(X30,X31))|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))&(X30!=k1_xboole_0|r2_hidden(X32,k1_funct_2(X30,X31))|(~v1_funct_1(X32)|~v1_funct_2(X32,X30,X31)|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(X30,X31)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_funct_2])])])).
% 0.19/0.50  cnf(c_0_29, plain, (v1_funct_2(X1,X2,X3)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_30, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_31, plain, (v1_funct_1(X1)|~r2_hidden(X1,k5_partfun1(X2,X3,X4))|~v1_funct_1(X4)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.50  cnf(c_0_32, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  cnf(c_0_33, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.50  fof(c_0_34, negated_conjecture, ((v1_funct_1(esk4_0)&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&~r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.19/0.50  fof(c_0_35, plain, ![X15]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 0.19/0.50  cnf(c_0_36, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.50  cnf(c_0_37, plain, (v1_xboole_0(X1)|v1_xboole_0(k5_partfun1(X1,X2,X3))|~v1_xboole_0(X2)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.50  fof(c_0_38, plain, ![X24, X25, X26]:(~v1_xboole_0(X24)|(~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(X25,X24)))|v1_xboole_0(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).
% 0.19/0.50  cnf(c_0_39, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_40, plain, (X1=k1_xboole_0|r2_hidden(X2,k1_funct_2(X3,X1))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.50  cnf(c_0_41, plain, (v1_funct_2(esk1_2(k5_partfun1(X1,X2,X3),X4),X1,X2)|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.19/0.50  cnf(c_0_42, plain, (m1_subset_1(esk1_2(k5_partfun1(X1,X2,X3),X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_30, c_0_25])).
% 0.19/0.50  cnf(c_0_43, plain, (v1_funct_1(esk1_2(k5_partfun1(X1,X2,X3),X4))|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 0.19/0.50  cnf(c_0_44, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.50  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_46, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.50  cnf(c_0_47, negated_conjecture, (~r1_tarski(k5_partfun1(esk2_0,esk3_0,esk4_0),k1_funct_2(esk2_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_48, plain, (v1_xboole_0(X1)|r1_tarski(k5_partfun1(X1,X2,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.50  cnf(c_0_49, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.19/0.50  cnf(c_0_50, plain, (v1_xboole_0(X2)|~v1_xboole_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.19/0.50  cnf(c_0_51, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_39])).
% 0.19/0.50  cnf(c_0_52, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.50  cnf(c_0_53, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.50  cnf(c_0_54, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(k5_partfun1(X2,X1,X3),X4),k1_funct_2(X2,X1))|r1_tarski(k5_partfun1(X2,X1,X3),X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42]), c_0_43])).
% 0.19/0.50  cnf(c_0_55, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.50  cnf(c_0_56, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_46])).
% 0.19/0.50  cnf(c_0_57, negated_conjecture, (v1_xboole_0(esk2_0)|~v1_xboole_0(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_45])])).
% 0.19/0.50  cnf(c_0_58, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])])).
% 0.19/0.50  cnf(c_0_59, plain, (X1=k1_xboole_0|r1_tarski(k5_partfun1(X2,X1,X3),k1_funct_2(X2,X1))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.50  cnf(c_0_60, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(esk1_2(X1,k2_zfmisc_1(esk2_0,esk3_0)),esk4_0)), inference(spm,[status(thm)],[c_0_53, c_0_55])).
% 0.19/0.50  cnf(c_0_61, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_50, c_0_20])).
% 0.19/0.50  cnf(c_0_62, plain, (r1_tarski(k1_xboole_0,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_56, c_0_25])).
% 0.19/0.50  cnf(c_0_63, negated_conjecture, (v1_xboole_0(esk2_0)|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.19/0.50  cnf(c_0_64, negated_conjecture, (esk3_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_59]), c_0_49]), c_0_45])])).
% 0.19/0.50  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_66, negated_conjecture, (r1_tarski(esk4_0,k2_zfmisc_1(esk2_0,esk3_0))), inference(spm,[status(thm)],[c_0_60, c_0_25])).
% 0.19/0.50  cnf(c_0_67, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_36, c_0_61])).
% 0.19/0.50  cnf(c_0_68, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_62, c_0_52])).
% 0.19/0.50  cnf(c_0_69, negated_conjecture, (v1_xboole_0(esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64]), c_0_46])])).
% 0.19/0.50  cnf(c_0_70, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~r1_tarski(k2_zfmisc_1(esk2_0,esk3_0),esk4_0)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.50  cnf(c_0_71, plain, (r1_tarski(k2_zfmisc_1(X1,X2),X3)|~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_67, c_0_58])).
% 0.19/0.50  fof(c_0_72, plain, ![X33, X34]:(~v1_funct_1(X34)|~v1_funct_2(X34,X33,X33)|~m1_subset_1(X34,k1_zfmisc_1(k2_zfmisc_1(X33,X33)))|r2_hidden(X34,k1_funct_2(X33,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_funct_2])])).
% 0.19/0.50  cnf(c_0_73, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_65, c_0_68])).
% 0.19/0.50  cnf(c_0_74, negated_conjecture, (r1_tarski(esk2_0,X1)), inference(spm,[status(thm)],[c_0_36, c_0_69])).
% 0.19/0.50  cnf(c_0_75, negated_conjecture, (k2_zfmisc_1(esk2_0,esk3_0)=esk4_0|~m1_subset_1(esk3_0,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.50  cnf(c_0_76, plain, (r2_hidden(X1,k1_funct_2(X2,X2))|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))), inference(split_conjunct,[status(thm)],[c_0_72])).
% 0.19/0.50  cnf(c_0_77, negated_conjecture, (esk2_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.50  cnf(c_0_78, negated_conjecture, (esk4_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_75, c_0_64]), c_0_51]), c_0_64]), c_0_46])])).
% 0.19/0.50  cnf(c_0_79, plain, (r2_hidden(esk1_2(k5_partfun1(X1,X1,X2),X3),k1_funct_2(X1,X1))|r1_tarski(k5_partfun1(X1,X1,X2),X3)|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_41]), c_0_42]), c_0_43])).
% 0.19/0.50  cnf(c_0_80, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.50  cnf(c_0_81, negated_conjecture, (~r1_tarski(k5_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_funct_2(k1_xboole_0,k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_64]), c_0_64]), c_0_77]), c_0_78]), c_0_77])).
% 0.19/0.50  cnf(c_0_82, plain, (r1_tarski(k5_partfun1(X1,X1,X2),k1_funct_2(X1,X1))|~v1_funct_1(X2)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))), inference(spm,[status(thm)],[c_0_53, c_0_79])).
% 0.19/0.50  cnf(c_0_83, negated_conjecture, (v1_funct_1(k1_xboole_0)), inference(rw,[status(thm)],[c_0_49, c_0_78])).
% 0.19/0.50  cnf(c_0_84, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_80])).
% 0.19/0.50  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83]), c_0_84]), c_0_46])]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 86
% 0.19/0.50  # Proof object clause steps            : 60
% 0.19/0.50  # Proof object formula steps           : 26
% 0.19/0.50  # Proof object conjectures             : 21
% 0.19/0.50  # Proof object clause conjectures      : 18
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 22
% 0.19/0.50  # Proof object initial formulas used   : 13
% 0.19/0.50  # Proof object generating inferences   : 33
% 0.19/0.50  # Proof object simplifying inferences  : 31
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 14
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 26
% 0.19/0.50  # Removed in clause preprocessing      : 0
% 0.19/0.50  # Initial clauses in saturation        : 26
% 0.19/0.50  # Processed clauses                    : 1612
% 0.19/0.50  # ...of these trivial                  : 25
% 0.19/0.50  # ...subsumed                          : 1081
% 0.19/0.50  # ...remaining for further processing  : 506
% 0.19/0.50  # Other redundant clauses eliminated   : 2
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 7
% 0.19/0.50  # Backward-rewritten                   : 125
% 0.19/0.50  # Generated clauses                    : 4777
% 0.19/0.50  # ...of the previous two non-trivial   : 4480
% 0.19/0.50  # Contextual simplify-reflections      : 16
% 0.19/0.50  # Paramodulations                      : 4773
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 4
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 347
% 0.19/0.50  #    Positive orientable unit clauses  : 11
% 0.19/0.50  #    Positive unorientable unit clauses: 0
% 0.19/0.50  #    Negative unit clauses             : 4
% 0.19/0.50  #    Non-unit-clauses                  : 332
% 0.19/0.50  # Current number of unprocessed clauses: 2739
% 0.19/0.50  # ...number of literals in the above   : 14210
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 157
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 25605
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 14718
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 1022
% 0.19/0.50  # Unit Clause-clause subsumption calls : 1518
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 19
% 0.19/0.50  # BW rewrite match successes           : 4
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 86435
% 0.19/0.51  
% 0.19/0.51  # -------------------------------------------------
% 0.19/0.51  # User time                : 0.167 s
% 0.19/0.51  # System time              : 0.005 s
% 0.19/0.51  # Total time               : 0.172 s
% 0.19/0.51  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
