%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:02:37 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  113 (1334 expanded)
%              Number of clauses        :   81 ( 529 expanded)
%              Number of leaves         :   16 ( 343 expanded)
%              Depth                    :   19
%              Number of atoms          :  361 (6027 expanded)
%              Number of equality atoms :   67 ( 861 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   36 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t31_funct_2,conjecture,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( v2_funct_1(X3)
          & k2_relset_1(X1,X2,X3) = X2 )
       => ( v1_funct_1(k2_funct_1(X3))
          & v1_funct_2(k2_funct_1(X3),X2,X1)
          & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(d18_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v4_relat_1(X2,X1)
      <=> r1_tarski(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(t9_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X2,X3)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(X4)
            & v1_funct_2(X4,X1,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( ( v1_funct_1(X3)
          & v1_funct_2(X3,X1,X2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( ( v2_funct_1(X3)
            & k2_relset_1(X1,X2,X3) = X2 )
         => ( v1_funct_1(k2_funct_1(X3))
            & v1_funct_2(k2_funct_1(X3),X2,X1)
            & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_funct_2])).

fof(c_0_17,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_18,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk3_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))
    & v2_funct_1(esk5_0)
    & k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0
    & ( ~ v1_funct_1(k2_funct_1(esk5_0))
      | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(X1,esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X20,X21] :
      ( ( k2_zfmisc_1(X20,X21) != k1_xboole_0
        | X20 = k1_xboole_0
        | X21 = k1_xboole_0 )
      & ( X20 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 )
      & ( X21 != k1_xboole_0
        | k2_zfmisc_1(X20,X21) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X16,X17] :
      ( ( r1_tarski(X16,X17)
        | X16 != X17 )
      & ( r1_tarski(X17,X16)
        | X16 != X17 )
      & ( ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X17,X16)
        | X16 = X17 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | ~ v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_32,plain,(
    ! [X42,X43,X44] :
      ( ( v4_relat_1(X44,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) )
      & ( v5_relat_1(X44,X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

fof(c_0_33,plain,(
    ! [X22,X23] :
      ( ( ~ m1_subset_1(X22,k1_zfmisc_1(X23))
        | r1_tarski(X22,X23) )
      & ( ~ r1_tarski(X22,X23)
        | m1_subset_1(X22,k1_zfmisc_1(X23)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_34,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | v1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_36,plain,(
    ! [X57] :
      ( ( v1_funct_1(X57)
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57) )
      & ( v1_funct_2(X57,k1_relat_1(X57),k2_relat_1(X57))
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57) )
      & ( m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X57),k2_relat_1(X57))))
        | ~ v1_relat_1(X57)
        | ~ v1_funct_1(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_37,plain,(
    ! [X38] :
      ( ( k2_relat_1(X38) = k1_relat_1(k2_funct_1(X38))
        | ~ v2_funct_1(X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) )
      & ( k1_relat_1(X38) = k2_relat_1(k2_funct_1(X38))
        | ~ v2_funct_1(X38)
        | ~ v1_relat_1(X38)
        | ~ v1_funct_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_38,plain,(
    ! [X35] :
      ( ( v1_relat_1(k2_funct_1(X35))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) )
      & ( v1_funct_1(k2_funct_1(X35))
        | ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_39,plain,(
    ! [X48,X49,X50] :
      ( ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | k2_relset_1(X48,X49,X50) = k2_relat_1(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk5_0)
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_42,plain,
    ( v4_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_34])).

cnf(c_0_45,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( k2_relset_1(esk3_0,esk4_0,esk5_0) = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_51,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_52,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_54,plain,
    ( v4_relat_1(X1,X2)
    | X3 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_30])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_56,plain,
    ( v1_relat_1(X1)
    | X2 != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_30])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( k2_relat_1(esk5_0) = esk4_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_20])])).

cnf(c_0_59,negated_conjecture,
    ( v2_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_61,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(spm,[status(thm)],[c_0_45,c_0_20])).

cnf(c_0_62,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_47]),c_0_48]),c_0_49])).

fof(c_0_63,plain,(
    ! [X27,X28] :
      ( ( ~ v4_relat_1(X28,X27)
        | r1_tarski(k1_relat_1(X28),X27)
        | ~ v1_relat_1(X28) )
      & ( ~ r1_tarski(k1_relat_1(X28),X27)
        | v4_relat_1(X28,X27)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).

cnf(c_0_64,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(X1))
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_53])).

cnf(c_0_65,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_67,plain,
    ( v4_relat_1(k1_xboole_0,X1)
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_68,plain,
    ( v1_relat_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_56,c_0_55])).

fof(c_0_69,plain,(
    ! [X58,X59,X60,X61] :
      ( ( v1_funct_1(X61)
        | X59 = k1_xboole_0
        | ~ r1_tarski(X59,X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( v1_funct_2(X61,X58,X60)
        | X59 = k1_xboole_0
        | ~ r1_tarski(X59,X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X60)))
        | X59 = k1_xboole_0
        | ~ r1_tarski(X59,X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( v1_funct_1(X61)
        | X58 != k1_xboole_0
        | ~ r1_tarski(X59,X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( v1_funct_2(X61,X58,X60)
        | X58 != k1_xboole_0
        | ~ r1_tarski(X59,X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) )
      & ( m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X60)))
        | X58 != k1_xboole_0
        | ~ r1_tarski(X59,X60)
        | ~ v1_funct_1(X61)
        | ~ v1_funct_2(X61,X58,X59)
        | ~ m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_71,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_73,plain,
    ( r1_tarski(k1_relat_1(X1),X2)
    | ~ v4_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,negated_conjecture,
    ( v4_relat_1(esk5_0,X1)
    | esk4_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_42,c_0_64])).

cnf(c_0_75,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( v4_relat_1(k1_xboole_0,X1) ),
    inference(er,[status(thm)],[c_0_67])).

cnf(c_0_77,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_68])).

cnf(c_0_78,plain,
    ( v1_funct_2(X1,X2,X3)
    | X2 != k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_80,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_71]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),X1)
    | esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_61])])).

cnf(c_0_82,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X2 != k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_83,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_66])).

cnf(c_0_84,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_31])).

cnf(c_0_85,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_76]),c_0_77])])).

cnf(c_0_86,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)
    | esk4_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])]),c_0_81])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))
    | esk4_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_79]),c_0_80])]),c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0)) = k2_funct_1(esk5_0)
    | ~ m1_subset_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0)),k1_zfmisc_1(k2_funct_1(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_79])).

cnf(c_0_90,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_84])).

cnf(c_0_91,plain,
    ( k1_xboole_0 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_75,c_0_84])).

cnf(c_0_92,plain,
    ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_85])).

cnf(c_0_93,negated_conjecture,
    ( esk4_0 != k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_88])).

cnf(c_0_94,plain,
    ( v1_funct_2(X1,X2,X3)
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_95,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_71]),c_0_48]),c_0_49])).

cnf(c_0_96,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_71]),c_0_48]),c_0_49])).

cnf(c_0_97,negated_conjecture,
    ( v4_relat_1(esk5_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_20])).

cnf(c_0_98,negated_conjecture,
    ( k2_funct_1(esk5_0) = k1_xboole_0
    | k1_relat_1(esk5_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_30]),c_0_90])])).

cnf(c_0_99,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_91,c_0_92])).

cnf(c_0_100,negated_conjecture,
    ( esk4_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_49]),c_0_60]),c_0_61])])).

cnf(c_0_101,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),X2)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_49]),c_0_96])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk5_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_97]),c_0_61])])).

cnf(c_0_103,negated_conjecture,
    ( k1_relat_1(esk5_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_98]),c_0_99]),c_0_58]),c_0_59]),c_0_60]),c_0_61])]),c_0_100])).

cnf(c_0_104,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | X4 = k1_xboole_0
    | ~ r1_tarski(X4,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_69])).

cnf(c_0_105,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),k1_relat_1(k2_funct_1(esk5_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_59]),c_0_60]),c_0_61])]),c_0_103])).

cnf(c_0_106,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2)))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_95]),c_0_49]),c_0_96])).

cnf(c_0_107,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_47]),c_0_58]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_108,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_102]),c_0_59]),c_0_60]),c_0_61])]),c_0_103])).

cnf(c_0_109,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0))
    | ~ m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_107])])).

cnf(c_0_110,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_47]),c_0_58]),c_0_59]),c_0_60]),c_0_61])])).

cnf(c_0_111,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109,c_0_110])])).

cnf(c_0_112,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_49]),c_0_60]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.47/0.66  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.47/0.66  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.47/0.66  #
% 0.47/0.66  # Preprocessing time       : 0.030 s
% 0.47/0.66  
% 0.47/0.66  # Proof found!
% 0.47/0.66  # SZS status Theorem
% 0.47/0.66  # SZS output start CNFRefutation
% 0.47/0.66  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.47/0.66  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.47/0.66  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.47/0.66  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.47/0.66  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.47/0.66  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.47/0.66  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.47/0.66  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 0.47/0.66  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.47/0.66  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.47/0.66  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.47/0.66  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.47/0.66  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.47/0.66  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.47/0.66  fof(d18_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v4_relat_1(X2,X1)<=>r1_tarski(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 0.47/0.66  fof(t9_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X2,X3)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(X4)&v1_funct_2(X4,X1,X3))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 0.47/0.66  fof(c_0_16, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.47/0.66  fof(c_0_17, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.47/0.66  fof(c_0_18, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk3_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0))))&((v2_funct_1(esk5_0)&k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0)&(~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.47/0.66  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.47/0.66  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk3_0,esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.66  fof(c_0_21, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.47/0.66  fof(c_0_22, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.47/0.66  cnf(c_0_23, negated_conjecture, (~r2_hidden(X1,esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.47/0.66  cnf(c_0_24, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.66  fof(c_0_25, plain, ![X20, X21]:((k2_zfmisc_1(X20,X21)!=k1_xboole_0|(X20=k1_xboole_0|X21=k1_xboole_0))&((X20!=k1_xboole_0|k2_zfmisc_1(X20,X21)=k1_xboole_0)&(X21!=k1_xboole_0|k2_zfmisc_1(X20,X21)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.47/0.66  fof(c_0_26, plain, ![X16, X17]:(((r1_tarski(X16,X17)|X16!=X17)&(r1_tarski(X17,X16)|X16!=X17))&(~r1_tarski(X16,X17)|~r1_tarski(X17,X16)|X16=X17)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.47/0.66  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.66  cnf(c_0_28, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.47/0.66  cnf(c_0_29, negated_conjecture, (v1_xboole_0(esk5_0)|~v1_xboole_0(k2_zfmisc_1(esk3_0,esk4_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.47/0.66  cnf(c_0_30, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.66  cnf(c_0_31, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.47/0.66  fof(c_0_32, plain, ![X42, X43, X44]:((v4_relat_1(X44,X42)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))&(v5_relat_1(X44,X43)|~m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 0.47/0.66  fof(c_0_33, plain, ![X22, X23]:((~m1_subset_1(X22,k1_zfmisc_1(X23))|r1_tarski(X22,X23))&(~r1_tarski(X22,X23)|m1_subset_1(X22,k1_zfmisc_1(X23)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.47/0.66  cnf(c_0_34, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.66  fof(c_0_35, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|v1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.47/0.66  fof(c_0_36, plain, ![X57]:(((v1_funct_1(X57)|(~v1_relat_1(X57)|~v1_funct_1(X57)))&(v1_funct_2(X57,k1_relat_1(X57),k2_relat_1(X57))|(~v1_relat_1(X57)|~v1_funct_1(X57))))&(m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X57),k2_relat_1(X57))))|(~v1_relat_1(X57)|~v1_funct_1(X57)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.47/0.66  fof(c_0_37, plain, ![X38]:((k2_relat_1(X38)=k1_relat_1(k2_funct_1(X38))|~v2_funct_1(X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))&(k1_relat_1(X38)=k2_relat_1(k2_funct_1(X38))|~v2_funct_1(X38)|(~v1_relat_1(X38)|~v1_funct_1(X38)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.47/0.66  fof(c_0_38, plain, ![X35]:((v1_relat_1(k2_funct_1(X35))|(~v1_relat_1(X35)|~v1_funct_1(X35)))&(v1_funct_1(k2_funct_1(X35))|(~v1_relat_1(X35)|~v1_funct_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.47/0.66  fof(c_0_39, plain, ![X48, X49, X50]:(~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|k2_relset_1(X48,X49,X50)=k2_relat_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.47/0.66  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.47/0.66  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk5_0)|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.47/0.66  cnf(c_0_42, plain, (v4_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.47/0.66  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.66  cnf(c_0_44, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_34])).
% 0.47/0.66  cnf(c_0_45, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.66  cnf(c_0_46, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.66  cnf(c_0_47, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.66  cnf(c_0_48, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.66  cnf(c_0_49, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.47/0.66  cnf(c_0_50, negated_conjecture, (k2_relset_1(esk3_0,esk4_0,esk5_0)=esk4_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.66  cnf(c_0_51, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.47/0.66  cnf(c_0_52, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.66  cnf(c_0_53, negated_conjecture, (r1_tarski(esk5_0,X1)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.47/0.66  cnf(c_0_54, plain, (v4_relat_1(X1,X2)|X3!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_42, c_0_30])).
% 0.47/0.66  cnf(c_0_55, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.47/0.66  cnf(c_0_56, plain, (v1_relat_1(X1)|X2!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_45, c_0_30])).
% 0.47/0.66  cnf(c_0_57, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_49])).
% 0.47/0.66  cnf(c_0_58, negated_conjecture, (k2_relat_1(esk5_0)=esk4_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_20])])).
% 0.47/0.66  cnf(c_0_59, negated_conjecture, (v2_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.66  cnf(c_0_60, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.66  cnf(c_0_61, negated_conjecture, (v1_relat_1(esk5_0)), inference(spm,[status(thm)],[c_0_45, c_0_20])).
% 0.47/0.66  cnf(c_0_62, plain, (v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_47]), c_0_48]), c_0_49])).
% 0.47/0.66  fof(c_0_63, plain, ![X27, X28]:((~v4_relat_1(X28,X27)|r1_tarski(k1_relat_1(X28),X27)|~v1_relat_1(X28))&(~r1_tarski(k1_relat_1(X28),X27)|v4_relat_1(X28,X27)|~v1_relat_1(X28))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d18_relat_1])])])).
% 0.47/0.66  cnf(c_0_64, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(X1))|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_53])).
% 0.47/0.66  cnf(c_0_65, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.66  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.47/0.66  cnf(c_0_67, plain, (v4_relat_1(k1_xboole_0,X1)|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.47/0.66  cnf(c_0_68, plain, (v1_relat_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_56, c_0_55])).
% 0.47/0.66  fof(c_0_69, plain, ![X58, X59, X60, X61]:((((v1_funct_1(X61)|X59=k1_xboole_0|~r1_tarski(X59,X60)|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))&(v1_funct_2(X61,X58,X60)|X59=k1_xboole_0|~r1_tarski(X59,X60)|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))))&(m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X60)))|X59=k1_xboole_0|~r1_tarski(X59,X60)|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))))&(((v1_funct_1(X61)|X58!=k1_xboole_0|~r1_tarski(X59,X60)|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59)))))&(v1_funct_2(X61,X58,X60)|X58!=k1_xboole_0|~r1_tarski(X59,X60)|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))))&(m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X60)))|X58!=k1_xboole_0|~r1_tarski(X59,X60)|(~v1_funct_1(X61)|~v1_funct_2(X61,X58,X59)|~m1_subset_1(X61,k1_zfmisc_1(k2_zfmisc_1(X58,X59))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_funct_2])])])).
% 0.47/0.66  cnf(c_0_70, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k2_relat_1(k2_funct_1(esk5_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_71, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.47/0.66  cnf(c_0_72, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k2_relat_1(k2_funct_1(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_58]), c_0_59]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_73, plain, (r1_tarski(k1_relat_1(X1),X2)|~v4_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.47/0.66  cnf(c_0_74, negated_conjecture, (v4_relat_1(esk5_0,X1)|esk4_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_42, c_0_64])).
% 0.47/0.66  cnf(c_0_75, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.47/0.66  cnf(c_0_76, plain, (v4_relat_1(k1_xboole_0,X1)), inference(er,[status(thm)],[c_0_67])).
% 0.47/0.66  cnf(c_0_77, plain, (v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_68])).
% 0.47/0.66  cnf(c_0_78, plain, (v1_funct_2(X1,X2,X3)|X2!=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.47/0.66  cnf(c_0_79, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_59]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_80, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,k1_relat_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_71]), c_0_59]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_81, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),X1)|esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_74]), c_0_61])])).
% 0.47/0.66  cnf(c_0_82, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X2!=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.47/0.66  cnf(c_0_83, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_75, c_0_66])).
% 0.47/0.66  cnf(c_0_84, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_40, c_0_31])).
% 0.47/0.66  cnf(c_0_85, plain, (r1_tarski(k1_relat_1(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_76]), c_0_77])])).
% 0.47/0.66  cnf(c_0_86, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.47/0.66  cnf(c_0_87, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,X1)|esk4_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])]), c_0_81])).
% 0.47/0.66  cnf(c_0_88, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,X1)))|esk4_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk5_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_79]), c_0_80])]), c_0_81])).
% 0.47/0.66  cnf(c_0_89, negated_conjecture, (k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0))=k2_funct_1(esk5_0)|~m1_subset_1(k2_zfmisc_1(esk4_0,k1_relat_1(esk5_0)),k1_zfmisc_1(k2_funct_1(esk5_0)))), inference(spm,[status(thm)],[c_0_83, c_0_79])).
% 0.47/0.66  cnf(c_0_90, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_84])).
% 0.47/0.66  cnf(c_0_91, plain, (k1_xboole_0=X1|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_75, c_0_84])).
% 0.47/0.66  cnf(c_0_92, plain, (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_43, c_0_85])).
% 0.47/0.66  cnf(c_0_93, negated_conjecture, (esk4_0!=k1_xboole_0|~v1_funct_1(k2_funct_1(esk5_0))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_88])).
% 0.47/0.66  cnf(c_0_94, plain, (v1_funct_2(X1,X2,X3)|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.47/0.66  cnf(c_0_95, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_71]), c_0_48]), c_0_49])).
% 0.47/0.66  cnf(c_0_96, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_71]), c_0_48]), c_0_49])).
% 0.47/0.66  cnf(c_0_97, negated_conjecture, (v4_relat_1(esk5_0,esk3_0)), inference(spm,[status(thm)],[c_0_42, c_0_20])).
% 0.47/0.66  cnf(c_0_98, negated_conjecture, (k2_funct_1(esk5_0)=k1_xboole_0|k1_relat_1(esk5_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89, c_0_30]), c_0_90])])).
% 0.47/0.66  cnf(c_0_99, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_91, c_0_92])).
% 0.47/0.66  cnf(c_0_100, negated_conjecture, (esk4_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_49]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_101, plain, (k1_relat_1(X1)=k1_xboole_0|v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),X2)|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_95]), c_0_49]), c_0_96])).
% 0.47/0.66  cnf(c_0_102, negated_conjecture, (r1_tarski(k1_relat_1(esk5_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_97]), c_0_61])])).
% 0.47/0.66  cnf(c_0_103, negated_conjecture, (k1_relat_1(esk5_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_98]), c_0_99]), c_0_58]), c_0_59]), c_0_60]), c_0_61])]), c_0_100])).
% 0.47/0.66  cnf(c_0_104, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|X4=k1_xboole_0|~r1_tarski(X4,X3)|~v1_funct_1(X1)|~v1_funct_2(X1,X2,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))), inference(split_conjunct,[status(thm)],[c_0_69])).
% 0.47/0.66  cnf(c_0_105, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),k1_relat_1(k2_funct_1(esk5_0)),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101, c_0_102]), c_0_59]), c_0_60]), c_0_61])]), c_0_103])).
% 0.47/0.66  cnf(c_0_106, plain, (k1_relat_1(X1)=k1_xboole_0|m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),X2)))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_104, c_0_95]), c_0_49]), c_0_96])).
% 0.47/0.66  cnf(c_0_107, negated_conjecture, (v1_funct_2(k2_funct_1(esk5_0),esk4_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_47]), c_0_58]), c_0_59]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_108, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk5_0)),esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_102]), c_0_59]), c_0_60]), c_0_61])]), c_0_103])).
% 0.47/0.66  cnf(c_0_109, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))|~m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86, c_0_107])])).
% 0.47/0.66  cnf(c_0_110, negated_conjecture, (m1_subset_1(k2_funct_1(esk5_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_47]), c_0_58]), c_0_59]), c_0_60]), c_0_61])])).
% 0.47/0.66  cnf(c_0_111, negated_conjecture, (~v1_funct_1(k2_funct_1(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_109, c_0_110])])).
% 0.47/0.66  cnf(c_0_112, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_49]), c_0_60]), c_0_61])]), ['proof']).
% 0.47/0.66  # SZS output end CNFRefutation
% 0.47/0.66  # Proof object total steps             : 113
% 0.47/0.66  # Proof object clause steps            : 81
% 0.47/0.66  # Proof object formula steps           : 32
% 0.47/0.66  # Proof object conjectures             : 37
% 0.47/0.66  # Proof object clause conjectures      : 34
% 0.47/0.66  # Proof object formula conjectures     : 3
% 0.47/0.66  # Proof object initial clauses used    : 29
% 0.47/0.66  # Proof object initial formulas used   : 16
% 0.47/0.66  # Proof object generating inferences   : 49
% 0.47/0.66  # Proof object simplifying inferences  : 85
% 0.47/0.66  # Training examples: 0 positive, 0 negative
% 0.47/0.66  # Parsed axioms                        : 25
% 0.47/0.66  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.66  # Initial clauses                      : 50
% 0.47/0.66  # Removed in clause preprocessing      : 4
% 0.47/0.66  # Initial clauses in saturation        : 46
% 0.47/0.66  # Processed clauses                    : 3496
% 0.47/0.66  # ...of these trivial                  : 31
% 0.47/0.66  # ...subsumed                          : 2354
% 0.47/0.66  # ...remaining for further processing  : 1111
% 0.47/0.66  # Other redundant clauses eliminated   : 4
% 0.47/0.66  # Clauses deleted for lack of memory   : 0
% 0.47/0.66  # Backward-subsumed                    : 102
% 0.47/0.66  # Backward-rewritten                   : 79
% 0.47/0.66  # Generated clauses                    : 14829
% 0.47/0.66  # ...of the previous two non-trivial   : 12392
% 0.47/0.66  # Contextual simplify-reflections      : 165
% 0.47/0.66  # Paramodulations                      : 14794
% 0.47/0.66  # Factorizations                       : 8
% 0.47/0.66  # Equation resolutions                 : 27
% 0.47/0.66  # Propositional unsat checks           : 0
% 0.47/0.66  #    Propositional check models        : 0
% 0.47/0.66  #    Propositional check unsatisfiable : 0
% 0.47/0.66  #    Propositional clauses             : 0
% 0.47/0.66  #    Propositional clauses after purity: 0
% 0.47/0.66  #    Propositional unsat core size     : 0
% 0.47/0.66  #    Propositional preprocessing time  : 0.000
% 0.47/0.66  #    Propositional encoding time       : 0.000
% 0.47/0.66  #    Propositional solver time         : 0.000
% 0.47/0.66  #    Success case prop preproc time    : 0.000
% 0.47/0.66  #    Success case prop encoding time   : 0.000
% 0.47/0.66  #    Success case prop solver time     : 0.000
% 0.47/0.66  # Current number of processed clauses  : 928
% 0.47/0.66  #    Positive orientable unit clauses  : 95
% 0.47/0.66  #    Positive unorientable unit clauses: 0
% 0.47/0.66  #    Negative unit clauses             : 9
% 0.47/0.66  #    Non-unit-clauses                  : 824
% 0.47/0.66  # Current number of unprocessed clauses: 8293
% 0.47/0.66  # ...number of literals in the above   : 31283
% 0.47/0.66  # Current number of archived formulas  : 0
% 0.47/0.66  # Current number of archived clauses   : 181
% 0.47/0.66  # Clause-clause subsumption calls (NU) : 102333
% 0.47/0.66  # Rec. Clause-clause subsumption calls : 33267
% 0.47/0.66  # Non-unit clause-clause subsumptions  : 1265
% 0.47/0.66  # Unit Clause-clause subsumption calls : 13314
% 0.47/0.66  # Rewrite failures with RHS unbound    : 42
% 0.47/0.66  # BW rewrite match attempts            : 274
% 0.47/0.66  # BW rewrite match successes           : 50
% 0.47/0.66  # Condensation attempts                : 0
% 0.47/0.66  # Condensation successes               : 0
% 0.47/0.66  # Termbank termtop insertions          : 225141
% 0.47/0.66  
% 0.47/0.66  # -------------------------------------------------
% 0.47/0.66  # User time                : 0.299 s
% 0.47/0.66  # System time              : 0.016 s
% 0.47/0.66  # Total time               : 0.316 s
% 0.47/0.66  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
