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
% DateTime   : Thu Dec  3 11:05:48 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 487 expanded)
%              Number of clauses        :   43 ( 192 expanded)
%              Number of leaves         :   11 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  234 (3070 expanded)
%              Number of equality atoms :   49 ( 731 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t77_funct_2,conjecture,(
    ! [X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_funct_2(X2,X1,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
     => ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X4,X1)
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
           => X3 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(t32_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X4)
          & r2_hidden(X3,X1) )
       => ( X2 = k1_xboole_0
          | k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3)) = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(d8_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,k1_relat_1(X1))
              & r2_hidden(X3,k1_relat_1(X1))
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_funct_2(X2,X1,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X4,X1)
                & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) )
             => X3 = X4 ) ) ) ),
    inference(assume_negation,[status(cth)],[t77_funct_2])).

fof(c_0_12,plain,(
    ! [X28,X29,X30,X31] :
      ( ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,X28,X29)
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))
      | ~ v2_funct_1(X31)
      | ~ r2_hidden(X30,X28)
      | X29 = k1_xboole_0
      | k1_funct_1(k2_funct_1(X31),k1_funct_1(X31,X30)) = X30 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).

fof(c_0_13,negated_conjecture,(
    ! [X36,X37] :
      ( v1_funct_1(esk4_0)
      & v1_funct_2(esk4_0,esk3_0,esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))
      & ( r2_hidden(esk5_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( r2_hidden(esk6_0,esk3_0)
        | ~ v2_funct_1(esk4_0) )
      & ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
        | ~ v2_funct_1(esk4_0) )
      & ( esk5_0 != esk6_0
        | ~ v2_funct_1(esk4_0) )
      & ( v2_funct_1(esk4_0)
        | ~ r2_hidden(X36,esk3_0)
        | ~ r2_hidden(X37,esk3_0)
        | k1_funct_1(esk4_0,X36) != k1_funct_1(esk4_0,X37)
        | X36 = X37 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).

cnf(c_0_14,plain,
    ( X3 = k1_xboole_0
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4)) = X4
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v2_funct_1(X1)
    | ~ r2_hidden(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_2(esk4_0,esk3_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | ~ v1_xboole_0(X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_19,plain,(
    ! [X10,X11] :
      ( ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
        | r1_tarski(X10,X11) )
      & ( ~ r1_tarski(X10,X11)
        | m1_subset_1(X10,k1_zfmisc_1(X11)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1)) = X1
    | esk3_0 = k1_xboole_0
    | ~ v2_funct_1(esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14,c_0_15]),c_0_16]),c_0_17])])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk6_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X25,X26,X27] :
      ( ( v4_relat_1(X27,X25)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) )
      & ( v5_relat_1(X27,X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_23,plain,(
    ! [X22,X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))
      | v1_relat_1(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,negated_conjecture,
    ( k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk6_0)) = esk6_0
    | esk3_0 = k1_xboole_0
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( k1_funct_1(esk4_0,esk5_0) = k1_funct_1(esk4_0,esk6_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_29,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_30,plain,(
    ! [X15,X16] :
      ( ( ~ v4_relat_1(X16,X15)
        | r1_tarski(k1_relat_1(X16),X15)
        | ~ v1_relat_1(X16) )
      & ( ~ r1_tarski(k1_relat_1(X16),X15)
        | v4_relat_1(X16,X15)
        | ~ v1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_31,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X3)
    | ~ v1_xboole_0(X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 != esk6_0
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,negated_conjecture,
    ( esk6_0 = k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))
    | esk3_0 = k1_xboole_0
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_38,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( v4_relat_1(esk4_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_17])).

cnf(c_0_40,negated_conjecture,
    ( v1_relat_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_17])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_funct_1(esk4_0)
    | ~ r1_tarski(esk3_0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk5_0,esk3_0)
    | ~ v2_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0)) != esk5_0
    | ~ v2_funct_1(esk4_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_25])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_47,negated_conjecture,
    ( ~ v2_funct_1(esk4_0)
    | ~ v1_xboole_0(esk3_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( esk3_0 = k1_xboole_0
    | ~ v2_funct_1(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( v2_funct_1(esk4_0)
    | X1 = X2
    | ~ r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X2,esk3_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(X1,esk3_0)
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_funct_1(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])])).

cnf(c_0_53,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

fof(c_0_54,plain,(
    ! [X17,X18,X19] :
      ( ( ~ v2_funct_1(X17)
        | ~ r2_hidden(X18,k1_relat_1(X17))
        | ~ r2_hidden(X19,k1_relat_1(X17))
        | k1_funct_1(X17,X18) != k1_funct_1(X17,X19)
        | X18 = X19
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk1_1(X17),k1_relat_1(X17))
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( r2_hidden(esk2_1(X17),k1_relat_1(X17))
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( k1_funct_1(X17,esk1_1(X17)) = k1_funct_1(X17,esk2_1(X17))
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) )
      & ( esk1_1(X17) != esk2_1(X17)
        | v2_funct_1(X17)
        | ~ v1_relat_1(X17)
        | ~ v1_funct_1(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).

cnf(c_0_55,negated_conjecture,
    ( X1 = X2
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_51])).

cnf(c_0_56,plain,
    ( k1_funct_1(X1,esk1_1(X1)) = k1_funct_1(X1,esk2_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_57,negated_conjecture,
    ( X1 = esk2_1(esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk1_1(esk4_0))
    | ~ r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_16]),c_0_40])]),c_0_52])).

cnf(c_0_58,plain,
    ( r2_hidden(esk2_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( X1 = esk2_1(esk4_0)
    | k1_funct_1(esk4_0,X1) != k1_funct_1(esk4_0,esk1_1(esk4_0))
    | ~ r2_hidden(X1,k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_16]),c_0_40])]),c_0_52])).

cnf(c_0_60,plain,
    ( v2_funct_1(X1)
    | esk1_1(X1) != esk2_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( esk2_1(esk4_0) = esk1_1(esk4_0)
    | ~ r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_16]),c_0_40])]),c_0_52])).

cnf(c_0_63,plain,
    ( r2_hidden(esk1_1(X1),k1_relat_1(X1))
    | v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_16]),c_0_40])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t77_funct_2, conjecture, ![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 0.19/0.38  fof(t32_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X4)&r2_hidden(X3,X1))=>(X2=k1_xboole_0|k1_funct_1(k2_funct_1(X4),k1_funct_1(X4,X3))=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 0.19/0.38  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.38  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.38  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.19/0.38  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.38  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.38  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.19/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.38  fof(d8_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)<=>![X2, X3]:(((r2_hidden(X2,k1_relat_1(X1))&r2_hidden(X3,k1_relat_1(X1)))&k1_funct_1(X1,X2)=k1_funct_1(X1,X3))=>X2=X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1, X2]:(((v1_funct_1(X2)&v1_funct_2(X2,X1,X1))&m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))))=>(v2_funct_1(X2)<=>![X3, X4]:(((r2_hidden(X3,X1)&r2_hidden(X4,X1))&k1_funct_1(X2,X3)=k1_funct_1(X2,X4))=>X3=X4)))), inference(assume_negation,[status(cth)],[t77_funct_2])).
% 0.19/0.38  fof(c_0_12, plain, ![X28, X29, X30, X31]:(~v1_funct_1(X31)|~v1_funct_2(X31,X28,X29)|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(X28,X29)))|(~v2_funct_1(X31)|~r2_hidden(X30,X28)|(X29=k1_xboole_0|k1_funct_1(k2_funct_1(X31),k1_funct_1(X31,X30))=X30))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_funct_2])])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, ![X36, X37]:(((v1_funct_1(esk4_0)&v1_funct_2(esk4_0,esk3_0,esk3_0))&m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0))))&(((((r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0))&(r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)))&(k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)))&(esk5_0!=esk6_0|~v2_funct_1(esk4_0)))&(v2_funct_1(esk4_0)|(~r2_hidden(X36,esk3_0)|~r2_hidden(X37,esk3_0)|k1_funct_1(esk4_0,X36)!=k1_funct_1(esk4_0,X37)|X36=X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])).
% 0.19/0.38  cnf(c_0_14, plain, (X3=k1_xboole_0|k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X4))=X4|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v2_funct_1(X1)|~r2_hidden(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_15, negated_conjecture, (v1_funct_2(esk4_0,esk3_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (v1_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_18, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|~v1_xboole_0(X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.38  fof(c_0_19, plain, ![X10, X11]:((~m1_subset_1(X10,k1_zfmisc_1(X11))|r1_tarski(X10,X11))&(~r1_tarski(X10,X11)|m1_subset_1(X10,k1_zfmisc_1(X11)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.38  cnf(c_0_20, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,X1))=X1|esk3_0=k1_xboole_0|~v2_funct_1(esk4_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_14, c_0_15]), c_0_16]), c_0_17])])).
% 0.19/0.38  cnf(c_0_21, negated_conjecture, (r2_hidden(esk6_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_22, plain, ![X25, X26, X27]:((v4_relat_1(X27,X25)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))&(v5_relat_1(X27,X26)|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(X25,X26))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.19/0.38  fof(c_0_23, plain, ![X22, X23, X24]:(~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(X22,X23)))|v1_relat_1(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.38  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_26, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.38  cnf(c_0_27, negated_conjecture, (k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk6_0))=esk6_0|esk3_0=k1_xboole_0|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  cnf(c_0_28, negated_conjecture, (k1_funct_1(esk4_0,esk5_0)=k1_funct_1(esk4_0,esk6_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_29, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  fof(c_0_30, plain, ![X15, X16]:((~v4_relat_1(X16,X15)|r1_tarski(k1_relat_1(X16),X15)|~v1_relat_1(X16))&(~r1_tarski(k1_relat_1(X16),X15)|v4_relat_1(X16,X15)|~v1_relat_1(X16))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.19/0.38  cnf(c_0_31, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.38  cnf(c_0_32, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_33, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X3)|~v1_xboole_0(X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.19/0.38  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (esk5_0!=esk6_0|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_36, negated_conjecture, (esk6_0=k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))|esk3_0=k1_xboole_0|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.38  cnf(c_0_37, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.38  cnf(c_0_38, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (v4_relat_1(esk4_0,esk3_0)), inference(spm,[status(thm)],[c_0_31, c_0_17])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (v1_relat_1(esk4_0)), inference(spm,[status(thm)],[c_0_32, c_0_17])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (~v2_funct_1(esk4_0)|~r1_tarski(esk3_0,X1)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_33, c_0_21])).
% 0.19/0.38  cnf(c_0_42, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(esk5_0,esk3_0)|~v2_funct_1(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (esk3_0=k1_xboole_0|k1_funct_1(k2_funct_1(esk4_0),k1_funct_1(esk4_0,esk5_0))!=esk5_0|~v2_funct_1(esk4_0)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_45, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_37, c_0_25])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r1_tarski(k1_relat_1(esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (~v2_funct_1(esk4_0)|~v1_xboole_0(esk3_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (esk3_0=k1_xboole_0|~v2_funct_1(esk4_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_43]), c_0_44])).
% 0.19/0.38  cnf(c_0_49, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (v2_funct_1(esk4_0)|X1=X2|~r2_hidden(X1,esk3_0)|~r2_hidden(X2,esk3_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(X1,esk3_0)|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.38  cnf(c_0_52, negated_conjecture, (~v2_funct_1(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49])])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (X1=X2|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,k1_relat_1(esk4_0))|~r2_hidden(X1,esk3_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.19/0.38  fof(c_0_54, plain, ![X17, X18, X19]:((~v2_funct_1(X17)|(~r2_hidden(X18,k1_relat_1(X17))|~r2_hidden(X19,k1_relat_1(X17))|k1_funct_1(X17,X18)!=k1_funct_1(X17,X19)|X18=X19)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&((((r2_hidden(esk1_1(X17),k1_relat_1(X17))|v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17)))&(r2_hidden(esk2_1(X17),k1_relat_1(X17))|v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(k1_funct_1(X17,esk1_1(X17))=k1_funct_1(X17,esk2_1(X17))|v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))&(esk1_1(X17)!=esk2_1(X17)|v2_funct_1(X17)|(~v1_relat_1(X17)|~v1_funct_1(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_funct_1])])])])])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (X1=X2|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,X2)|~r2_hidden(X2,k1_relat_1(esk4_0))|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_51])).
% 0.19/0.38  cnf(c_0_56, plain, (k1_funct_1(X1,esk1_1(X1))=k1_funct_1(X1,esk2_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (X1=esk2_1(esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk1_1(esk4_0))|~r2_hidden(esk2_1(esk4_0),k1_relat_1(esk4_0))|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_16]), c_0_40])]), c_0_52])).
% 0.19/0.38  cnf(c_0_58, plain, (r2_hidden(esk2_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_59, negated_conjecture, (X1=esk2_1(esk4_0)|k1_funct_1(esk4_0,X1)!=k1_funct_1(esk4_0,esk1_1(esk4_0))|~r2_hidden(X1,k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_16]), c_0_40])]), c_0_52])).
% 0.19/0.38  cnf(c_0_60, plain, (v2_funct_1(X1)|esk1_1(X1)!=esk2_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_61, negated_conjecture, (esk2_1(esk4_0)=esk1_1(esk4_0)|~r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0))), inference(er,[status(thm)],[c_0_59])).
% 0.19/0.38  cnf(c_0_62, negated_conjecture, (~r2_hidden(esk1_1(esk4_0),k1_relat_1(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_16]), c_0_40])]), c_0_52])).
% 0.19/0.38  cnf(c_0_63, plain, (r2_hidden(esk1_1(X1),k1_relat_1(X1))|v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.38  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_63]), c_0_16]), c_0_40])]), c_0_52]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 65
% 0.19/0.38  # Proof object clause steps            : 43
% 0.19/0.38  # Proof object formula steps           : 22
% 0.19/0.38  # Proof object conjectures             : 30
% 0.19/0.38  # Proof object clause conjectures      : 27
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 21
% 0.19/0.38  # Proof object initial formulas used   : 11
% 0.19/0.38  # Proof object generating inferences   : 21
% 0.19/0.38  # Proof object simplifying inferences  : 26
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 27
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 27
% 0.19/0.38  # Processed clauses                    : 152
% 0.19/0.38  # ...of these trivial                  : 1
% 0.19/0.38  # ...subsumed                          : 31
% 0.19/0.38  # ...remaining for further processing  : 120
% 0.19/0.38  # Other redundant clauses eliminated   : 2
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 6
% 0.19/0.38  # Backward-rewritten                   : 2
% 0.19/0.38  # Generated clauses                    : 132
% 0.19/0.38  # ...of the previous two non-trivial   : 118
% 0.19/0.38  # Contextual simplify-reflections      : 2
% 0.19/0.38  # Paramodulations                      : 120
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 5
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 81
% 0.19/0.38  #    Positive orientable unit clauses  : 21
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 5
% 0.19/0.38  #    Non-unit-clauses                  : 55
% 0.19/0.38  # Current number of unprocessed clauses: 13
% 0.19/0.38  # ...number of literals in the above   : 45
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 35
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 530
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 296
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 14
% 0.19/0.38  # Unit Clause-clause subsumption calls : 351
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 4
% 0.19/0.38  # BW rewrite match successes           : 1
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 4122
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.037 s
% 0.19/0.38  # System time              : 0.002 s
% 0.19/0.38  # Total time               : 0.039 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
