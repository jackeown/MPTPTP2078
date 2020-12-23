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
% DateTime   : Thu Dec  3 11:02:51 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   84 (1746 expanded)
%              Number of clauses        :   55 ( 643 expanded)
%              Number of leaves         :   15 ( 440 expanded)
%              Depth                    :   12
%              Number of atoms          :  266 (8774 expanded)
%              Number of equality atoms :   86 (1575 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

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

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_15,negated_conjecture,(
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

fof(c_0_16,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_relset_1(X38,X39,X40) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

fof(c_0_17,negated_conjecture,
    ( v1_funct_1(esk9_0)
    & v1_funct_2(esk9_0,esk7_0,esk8_0)
    & m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))
    & v2_funct_1(esk9_0)
    & k2_relset_1(esk7_0,esk8_0,esk9_0) = esk8_0
    & ( ~ v1_funct_1(k2_funct_1(esk9_0))
      | ~ v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)
      | ~ m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).

fof(c_0_18,plain,(
    ! [X52] :
      ( ( v1_funct_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,k1_relat_1(X52),k2_relat_1(X52))
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),k2_relat_1(X52))))
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_19,plain,(
    ! [X34] :
      ( ( k2_relat_1(X34) = k1_relat_1(k2_funct_1(X34))
        | ~ v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) )
      & ( k1_relat_1(X34) = k2_relat_1(k2_funct_1(X34))
        | ~ v2_funct_1(X34)
        | ~ v1_relat_1(X34)
        | ~ v1_funct_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_20,plain,(
    ! [X32] :
      ( ( v1_relat_1(k2_funct_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) )
      & ( v1_funct_1(k2_funct_1(X32))
        | ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_21,plain,(
    ! [X44,X45,X46] :
      ( ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X45 = k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X44 = k1_relset_1(X44,X45,X46)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X44 != k1_relset_1(X44,X45,X46)
        | v1_funct_2(X46,X44,X45)
        | X44 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( ~ v1_funct_2(X46,X44,X45)
        | X46 = k1_xboole_0
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) )
      & ( X46 != k1_xboole_0
        | v1_funct_2(X46,X44,X45)
        | X44 = k1_xboole_0
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_22,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_24,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))
      | v1_relat_1(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_25,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk9_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,negated_conjecture,
    ( k1_relset_1(esk7_0,esk8_0,esk9_0) = k1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

fof(c_0_33,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k2_relset_1(X41,X42,X43) = k2_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_34,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk9_0))
    | ~ v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)
    | ~ m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( v1_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( k1_relat_1(esk9_0) = esk7_0
    | esk8_0 = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_30])]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( v2_funct_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_23])).

cnf(c_0_40,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( k2_relset_1(esk7_0,esk8_0,esk9_0) = esk8_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_42,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_43,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_45,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)
    | ~ v1_relat_1(esk9_0)
    | ~ m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_35])])).

cnf(c_0_46,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk9_0),k1_relat_1(k2_funct_1(esk9_0)),esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_35]),c_0_39])])).

cnf(c_0_47,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,negated_conjecture,
    ( k2_relat_1(esk9_0) = esk8_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_23]),c_0_41])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_51,plain,(
    ! [X31] :
      ( ( k1_relat_1(X31) != k1_xboole_0
        | X31 = k1_xboole_0
        | ~ v1_relat_1(X31) )
      & ( k2_relat_1(X31) != k1_xboole_0
        | X31 = k1_xboole_0
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_52,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_26]),c_0_27]),c_0_28])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)
    | ~ m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48]),c_0_38]),c_0_35]),c_0_39])])).

fof(c_0_55,plain,(
    ! [X16,X17] :
      ( ( k2_zfmisc_1(X16,X17) != k1_xboole_0
        | X16 = k1_xboole_0
        | X17 = k1_xboole_0 )
      & ( X16 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 )
      & ( X17 != k1_xboole_0
        | k2_zfmisc_1(X16,X17) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_56,plain,(
    ! [X18,X19] :
      ( ( ~ m1_subset_1(X18,k1_zfmisc_1(X19))
        | r1_tarski(X18,X19) )
      & ( ~ r1_tarski(X18,X19)
        | m1_subset_1(X18,k1_zfmisc_1(X19)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_59,plain,
    ( X1 = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_60,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk9_0)),esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_37]),c_0_38]),c_0_35]),c_0_39])])).

cnf(c_0_61,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | ~ m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_62,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_64,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_67,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_48]),c_0_39])])).

cnf(c_0_68,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_47]),c_0_48]),c_0_38]),c_0_35]),c_0_39])]),c_0_61])).

cnf(c_0_69,plain,
    ( k2_funct_1(X1) = k1_xboole_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_47]),c_0_27])).

cnf(c_0_70,plain,
    ( v1_funct_2(X3,X1,X2)
    | X1 != k1_relset_1(X1,X2,X3)
    | X1 != k1_xboole_0
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_71,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_50])).

cnf(c_0_75,negated_conjecture,
    ( esk9_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67,c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( k2_funct_1(esk9_0) = k1_xboole_0
    | esk8_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_48]),c_0_38]),c_0_35]),c_0_39])])).

cnf(c_0_77,plain,
    ( v1_funct_2(X1,k1_xboole_0,X2)
    | k1_relset_1(k1_xboole_0,X2,X1) != k1_xboole_0
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_70]),c_0_71])).

cnf(c_0_78,plain,
    ( k1_relset_1(X1,X2,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_72]),c_0_73])).

cnf(c_0_79,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_74])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk7_0)
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53,c_0_68]),c_0_68]),c_0_71]),c_0_75]),c_0_75])).

cnf(c_0_81,negated_conjecture,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_68])]),c_0_75])).

cnf(c_0_82,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_79])])).

cnf(c_0_83,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81]),c_0_82]),c_0_81]),c_0_79])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___110_C45_F1_PI_SE_CS_SP_PS_S4S
% 0.14/0.39  # and selection function SelectNewComplexAHPNS.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.029 s
% 0.14/0.39  # Presaturation interreduction done
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t31_funct_2, conjecture, ![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 0.14/0.39  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 0.14/0.39  fof(t3_funct_2, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>((v1_funct_1(X1)&v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1)))&m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 0.14/0.39  fof(t55_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v2_funct_1(X1)=>(k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))&k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 0.14/0.39  fof(dt_k2_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>(v1_relat_1(k2_funct_1(X1))&v1_funct_1(k2_funct_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 0.14/0.39  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 0.14/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.14/0.39  fof(redefinition_k2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k2_relset_1(X1,X2,X3)=k2_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 0.14/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.14/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.14/0.39  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.14/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.14/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.14/0.39  fof(c_0_15, negated_conjecture, ~(![X1, X2, X3]:(((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>((v2_funct_1(X3)&k2_relset_1(X1,X2,X3)=X2)=>((v1_funct_1(k2_funct_1(X3))&v1_funct_2(k2_funct_1(X3),X2,X1))&m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))))))), inference(assume_negation,[status(cth)],[t31_funct_2])).
% 0.14/0.39  fof(c_0_16, plain, ![X38, X39, X40]:(~m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))|k1_relset_1(X38,X39,X40)=k1_relat_1(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 0.14/0.39  fof(c_0_17, negated_conjecture, (((v1_funct_1(esk9_0)&v1_funct_2(esk9_0,esk7_0,esk8_0))&m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0))))&((v2_funct_1(esk9_0)&k2_relset_1(esk7_0,esk8_0,esk9_0)=esk8_0)&(~v1_funct_1(k2_funct_1(esk9_0))|~v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)|~m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_15])])])).
% 0.14/0.39  fof(c_0_18, plain, ![X52]:(((v1_funct_1(X52)|(~v1_relat_1(X52)|~v1_funct_1(X52)))&(v1_funct_2(X52,k1_relat_1(X52),k2_relat_1(X52))|(~v1_relat_1(X52)|~v1_funct_1(X52))))&(m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),k2_relat_1(X52))))|(~v1_relat_1(X52)|~v1_funct_1(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).
% 0.14/0.39  fof(c_0_19, plain, ![X34]:((k2_relat_1(X34)=k1_relat_1(k2_funct_1(X34))|~v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))&(k1_relat_1(X34)=k2_relat_1(k2_funct_1(X34))|~v2_funct_1(X34)|(~v1_relat_1(X34)|~v1_funct_1(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).
% 0.14/0.39  fof(c_0_20, plain, ![X32]:((v1_relat_1(k2_funct_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32)))&(v1_funct_1(k2_funct_1(X32))|(~v1_relat_1(X32)|~v1_funct_1(X32)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).
% 0.14/0.39  fof(c_0_21, plain, ![X44, X45, X46]:((((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X45=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))&((~v1_funct_2(X46,X44,X45)|X44=k1_relset_1(X44,X45,X46)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X44!=k1_relset_1(X44,X45,X46)|v1_funct_2(X46,X44,X45)|X44!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))))&((~v1_funct_2(X46,X44,X45)|X46=k1_xboole_0|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45))))&(X46!=k1_xboole_0|v1_funct_2(X46,X44,X45)|X44=k1_xboole_0|X45!=k1_xboole_0|~m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X44,X45)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 0.14/0.39  cnf(c_0_22, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk9_0,k1_zfmisc_1(k2_zfmisc_1(esk7_0,esk8_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  fof(c_0_24, plain, ![X35, X36, X37]:(~m1_subset_1(X37,k1_zfmisc_1(k2_zfmisc_1(X35,X36)))|v1_relat_1(X37)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.14/0.39  cnf(c_0_25, plain, (v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_26, plain, (k1_relat_1(X1)=k2_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_27, plain, (v1_relat_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_28, plain, (v1_funct_1(k2_funct_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_29, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_30, negated_conjecture, (v1_funct_2(esk9_0,esk7_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_31, negated_conjecture, (k1_relset_1(esk7_0,esk8_0,esk9_0)=k1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.39  cnf(c_0_32, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.14/0.39  fof(c_0_33, plain, ![X41, X42, X43]:(~m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))|k2_relset_1(X41,X42,X43)=k2_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).
% 0.14/0.39  cnf(c_0_34, negated_conjecture, (~v1_funct_1(k2_funct_1(esk9_0))|~v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)|~m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_35, negated_conjecture, (v1_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_36, plain, (v1_funct_2(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.39  cnf(c_0_37, negated_conjecture, (k1_relat_1(esk9_0)=esk7_0|esk8_0=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_23]), c_0_30])]), c_0_31])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (v2_funct_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk9_0)), inference(spm,[status(thm)],[c_0_32, c_0_23])).
% 0.14/0.39  cnf(c_0_40, plain, (k2_relset_1(X2,X3,X1)=k2_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.39  cnf(c_0_41, negated_conjecture, (k2_relset_1(esk7_0,esk8_0,esk9_0)=esk8_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.39  fof(c_0_42, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.14/0.39  fof(c_0_43, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  cnf(c_0_44, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.14/0.39  cnf(c_0_45, negated_conjecture, (~v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)|~v1_relat_1(esk9_0)|~m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_28]), c_0_35])])).
% 0.14/0.39  cnf(c_0_46, negated_conjecture, (esk8_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk9_0),k1_relat_1(k2_funct_1(esk9_0)),esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_35]), c_0_39])])).
% 0.14/0.39  cnf(c_0_47, plain, (k2_relat_1(X1)=k1_relat_1(k2_funct_1(X1))|~v2_funct_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.39  cnf(c_0_48, negated_conjecture, (k2_relat_1(esk9_0)=esk8_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_23]), c_0_41])).
% 0.14/0.39  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.14/0.39  cnf(c_0_50, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.39  fof(c_0_51, plain, ![X31]:((k1_relat_1(X31)!=k1_xboole_0|X31=k1_xboole_0|~v1_relat_1(X31))&(k2_relat_1(X31)!=k1_xboole_0|X31=k1_xboole_0|~v1_relat_1(X31))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.14/0.39  cnf(c_0_52, plain, (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(X1)),k1_relat_1(X1))))|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_26]), c_0_27]), c_0_28])).
% 0.14/0.39  cnf(c_0_53, negated_conjecture, (~v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)|~m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_39])])).
% 0.14/0.39  cnf(c_0_54, negated_conjecture, (esk8_0=k1_xboole_0|v1_funct_2(k2_funct_1(esk9_0),esk8_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48]), c_0_38]), c_0_35]), c_0_39])])).
% 0.14/0.39  fof(c_0_55, plain, ![X16, X17]:((k2_zfmisc_1(X16,X17)!=k1_xboole_0|(X16=k1_xboole_0|X17=k1_xboole_0))&((X16!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0)&(X17!=k1_xboole_0|k2_zfmisc_1(X16,X17)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.14/0.39  fof(c_0_56, plain, ![X18, X19]:((~m1_subset_1(X18,k1_zfmisc_1(X19))|r1_tarski(X18,X19))&(~r1_tarski(X18,X19)|m1_subset_1(X18,k1_zfmisc_1(X19)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.14/0.39  cnf(c_0_57, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.14/0.39  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.14/0.39  cnf(c_0_59, plain, (X1=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.39  cnf(c_0_60, negated_conjecture, (esk8_0=k1_xboole_0|m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(esk9_0)),esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_37]), c_0_38]), c_0_35]), c_0_39])])).
% 0.14/0.39  cnf(c_0_61, negated_conjecture, (esk8_0=k1_xboole_0|~m1_subset_1(k2_funct_1(esk9_0),k1_zfmisc_1(k2_zfmisc_1(esk8_0,esk7_0)))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.14/0.39  cnf(c_0_62, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.14/0.39  cnf(c_0_63, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.14/0.39  cnf(c_0_64, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.14/0.39  cnf(c_0_65, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.14/0.39  cnf(c_0_66, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.14/0.39  cnf(c_0_67, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_48]), c_0_39])])).
% 0.14/0.39  cnf(c_0_68, negated_conjecture, (esk8_0=k1_xboole_0), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_47]), c_0_48]), c_0_38]), c_0_35]), c_0_39])]), c_0_61])).
% 0.14/0.39  cnf(c_0_69, plain, (k2_funct_1(X1)=k1_xboole_0|k2_relat_1(X1)!=k1_xboole_0|~v2_funct_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_47]), c_0_27])).
% 0.14/0.39  cnf(c_0_70, plain, (v1_funct_2(X3,X1,X2)|X1!=k1_relset_1(X1,X2,X3)|X1!=k1_xboole_0|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_71, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_63])).
% 0.14/0.39  cnf(c_0_72, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.14/0.39  cnf(c_0_73, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.14/0.39  cnf(c_0_74, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_66, c_0_50])).
% 0.14/0.39  cnf(c_0_75, negated_conjecture, (esk9_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_67, c_0_68])])).
% 0.14/0.39  cnf(c_0_76, negated_conjecture, (k2_funct_1(esk9_0)=k1_xboole_0|esk8_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_48]), c_0_38]), c_0_35]), c_0_39])])).
% 0.14/0.39  cnf(c_0_77, plain, (v1_funct_2(X1,k1_xboole_0,X2)|k1_relset_1(k1_xboole_0,X2,X1)!=k1_xboole_0|~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_70]), c_0_71])).
% 0.14/0.39  cnf(c_0_78, plain, (k1_relset_1(X1,X2,k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_72]), c_0_73])).
% 0.14/0.39  cnf(c_0_79, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_64, c_0_74])).
% 0.14/0.39  cnf(c_0_80, negated_conjecture, (~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,esk7_0)|~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_53, c_0_68]), c_0_68]), c_0_71]), c_0_75]), c_0_75])).
% 0.14/0.39  cnf(c_0_81, negated_conjecture, (k2_funct_1(k1_xboole_0)=k1_xboole_0), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_68])]), c_0_75])).
% 0.14/0.39  cnf(c_0_82, plain, (v1_funct_2(k1_xboole_0,k1_xboole_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_79])])).
% 0.14/0.39  cnf(c_0_83, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81]), c_0_82]), c_0_81]), c_0_79])]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 84
% 0.14/0.39  # Proof object clause steps            : 55
% 0.14/0.39  # Proof object formula steps           : 29
% 0.14/0.39  # Proof object conjectures             : 26
% 0.14/0.39  # Proof object clause conjectures      : 23
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 26
% 0.14/0.39  # Proof object initial formulas used   : 15
% 0.14/0.39  # Proof object generating inferences   : 22
% 0.14/0.39  # Proof object simplifying inferences  : 59
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 21
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 53
% 0.14/0.39  # Removed in clause preprocessing      : 2
% 0.14/0.39  # Initial clauses in saturation        : 51
% 0.14/0.39  # Processed clauses                    : 245
% 0.14/0.39  # ...of these trivial                  : 13
% 0.14/0.39  # ...subsumed                          : 15
% 0.14/0.39  # ...remaining for further processing  : 217
% 0.14/0.39  # Other redundant clauses eliminated   : 13
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 2
% 0.14/0.39  # Backward-rewritten                   : 54
% 0.14/0.39  # Generated clauses                    : 327
% 0.14/0.39  # ...of the previous two non-trivial   : 241
% 0.14/0.39  # Contextual simplify-reflections      : 11
% 0.14/0.39  # Paramodulations                      : 315
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 13
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 102
% 0.14/0.39  #    Positive orientable unit clauses  : 43
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 0
% 0.14/0.39  #    Non-unit-clauses                  : 59
% 0.14/0.39  # Current number of unprocessed clauses: 86
% 0.14/0.39  # ...number of literals in the above   : 288
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 108
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 1213
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 714
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 27
% 0.14/0.39  # Unit Clause-clause subsumption calls : 266
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 90
% 0.14/0.39  # BW rewrite match successes           : 12
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 7468
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.040 s
% 0.14/0.39  # System time              : 0.006 s
% 0.14/0.39  # Total time               : 0.046 s
% 0.14/0.39  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
