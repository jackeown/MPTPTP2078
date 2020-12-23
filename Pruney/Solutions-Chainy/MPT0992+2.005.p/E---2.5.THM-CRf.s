%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:03:35 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 669 expanded)
%              Number of clauses        :   74 ( 285 expanded)
%              Number of leaves         :   19 ( 167 expanded)
%              Depth                    :   13
%              Number of atoms          :  327 (2877 expanded)
%              Number of equality atoms :   82 ( 804 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_funct_2,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

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

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(redefinition_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => k2_partfun1(X1,X2,X3,X4) = k7_relat_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(t4_subset_1,axiom,(
    ! [X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(t11_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( ( r1_tarski(k1_relat_1(X3),X1)
          & r1_tarski(k2_relat_1(X3),X2) )
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(d19_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( v5_relat_1(X2,X1)
      <=> r1_tarski(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

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

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(t91_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X1,k1_relat_1(X2))
       => k1_relat_1(k7_relat_1(X2,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(cc2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( v4_relat_1(X3,X1)
        & v5_relat_1(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( v1_funct_1(X4)
          & v1_funct_2(X4,X1,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
       => ( r1_tarski(X3,X1)
         => ( ( X2 = k1_xboole_0
              & X1 != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
              & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
              & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_funct_2])).

fof(c_0_20,negated_conjecture,
    ( v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,esk2_0,esk3_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))
    & r1_tarski(esk4_0,esk2_0)
    & ( esk3_0 != k1_xboole_0
      | esk2_0 = k1_xboole_0 )
    & ( ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))
      | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
      | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22] :
      ( ~ r2_hidden(X20,X21)
      | ~ m1_subset_1(X21,k1_zfmisc_1(X22))
      | ~ v1_xboole_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_22,plain,(
    ! [X12,X13] :
      ( ( k2_zfmisc_1(X12,X13) != k1_xboole_0
        | X12 = k1_xboole_0
        | X13 = k1_xboole_0 )
      & ( X12 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 )
      & ( X13 != k1_xboole_0
        | k2_zfmisc_1(X12,X13) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_23,plain,(
    ! [X11] :
      ( ~ r1_tarski(X11,k1_xboole_0)
      | X11 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( esk2_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_29,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_30,plain,(
    ! [X15,X16] :
      ( ( ~ m1_subset_1(X15,k1_zfmisc_1(X16))
        | r1_tarski(X15,X16) )
      & ( ~ r1_tarski(X15,X16)
        | m1_subset_1(X15,k1_zfmisc_1(X16)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_31,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk4_0,k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_36,plain,(
    ! [X27,X28] : v1_relat_1(k2_zfmisc_1(X27,X28)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_38,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_40,plain,(
    ! [X29,X30] :
      ( ~ v1_relat_1(X30)
      | r1_tarski(k7_relat_1(X30,X29),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( esk4_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_43,plain,(
    ! [X48,X49,X50,X51] :
      ( ( v1_funct_1(k2_partfun1(X48,X49,X50,X51))
        | ~ v1_funct_1(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) )
      & ( m1_subset_1(k2_partfun1(X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
        | ~ v1_funct_1(X50)
        | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_44,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ r2_hidden(X1,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_25]),c_0_34]),c_0_35])])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_46,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_49,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

fof(c_0_50,plain,(
    ! [X23,X24] :
      ( ~ v1_relat_1(X23)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | v1_relat_1(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_51,plain,(
    ! [X52,X53,X54,X55] :
      ( ~ v1_funct_1(X54)
      | ~ m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))
      | k2_partfun1(X52,X53,X54,X55) = k7_relat_1(X54,X55) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).

cnf(c_0_52,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0))
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_34])).

cnf(c_0_53,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_54,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk5_0,X1)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_56,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_57,plain,(
    ! [X14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)) ),
    inference(variable_rename,[status(thm)],[t4_subset_1])).

cnf(c_0_58,negated_conjecture,
    ( v1_funct_2(esk5_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_59,plain,(
    ! [X42,X43,X44] :
      ( ~ v1_relat_1(X44)
      | ~ r1_tarski(k1_relat_1(X44),X42)
      | ~ r1_tarski(k2_relat_1(X44),X43)
      | m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).

fof(c_0_60,plain,(
    ! [X25,X26] :
      ( ( ~ v5_relat_1(X26,X25)
        | r1_tarski(k2_relat_1(X26),X25)
        | ~ v1_relat_1(X26) )
      & ( ~ r1_tarski(k2_relat_1(X26),X25)
        | v5_relat_1(X26,X25)
        | ~ v1_relat_1(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_27])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X1,k7_relat_1(X2,X3)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_49])).

cnf(c_0_64,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_65,plain,
    ( k2_partfun1(X2,X3,X1,X4) = k7_relat_1(X1,X4)
    | ~ v1_funct_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

fof(c_0_66,plain,(
    ! [X45,X46,X47] :
      ( ( ~ v1_funct_2(X47,X45,X46)
        | X45 = k1_relset_1(X45,X46,X47)
        | X46 = k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X45 != k1_relset_1(X45,X46,X47)
        | v1_funct_2(X47,X45,X46)
        | X46 = k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ v1_funct_2(X47,X45,X46)
        | X45 = k1_relset_1(X45,X46,X47)
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X45 != k1_relset_1(X45,X46,X47)
        | v1_funct_2(X47,X45,X46)
        | X45 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( ~ v1_funct_2(X47,X45,X46)
        | X47 = k1_xboole_0
        | X45 = k1_xboole_0
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) )
      & ( X47 != k1_xboole_0
        | v1_funct_2(X47,X45,X46)
        | X45 = k1_xboole_0
        | X46 != k1_xboole_0
        | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

fof(c_0_67,plain,(
    ! [X39,X40,X41] :
      ( ~ m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
      | k1_relset_1(X39,X40,X41) = k1_relat_1(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_68,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_54]),c_0_27])])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = k1_xboole_0
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_31,c_0_55])).

cnf(c_0_70,plain,
    ( k7_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_49]),c_0_56])])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_2(esk5_0,k1_xboole_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_58,c_0_25])).

cnf(c_0_73,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2)
    | ~ r1_tarski(k2_relat_1(X1),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_74,plain,
    ( r1_tarski(k2_relat_1(X1),X2)
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_75,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_76,negated_conjecture,
    ( r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))
    | ~ r2_hidden(esk1_2(X1,k2_zfmisc_1(esk2_0,esk3_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_77,plain,
    ( r2_hidden(esk1_2(k7_relat_1(X1,X2),X3),X1)
    | r1_tarski(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_63,c_0_45])).

cnf(c_0_78,negated_conjecture,
    ( v1_relat_1(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_27]),c_0_46])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_53]),c_0_54]),c_0_27])])).

cnf(c_0_80,plain,
    ( k2_partfun1(X1,X2,X3,X4) = k2_partfun1(X5,X6,X3,X4)
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_65])).

cnf(c_0_81,plain,
    ( v1_funct_2(X3,X1,X2)
    | X2 = k1_xboole_0
    | X1 != k1_relset_1(X1,X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_82,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

fof(c_0_83,plain,(
    ! [X31,X32] :
      ( ~ v1_relat_1(X32)
      | ~ r1_tarski(X31,k1_relat_1(X32))
      | k1_relat_1(k7_relat_1(X32,X31)) = X31 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).

cnf(c_0_84,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_85,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_funct_2(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_86,plain,
    ( k2_partfun1(X1,X2,k1_xboole_0,X3) = k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_65]),c_0_71])])).

cnf(c_0_87,negated_conjecture,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_72,c_0_69])).

cnf(c_0_88,negated_conjecture,
    ( v1_funct_1(k1_xboole_0)
    | esk3_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_69])).

cnf(c_0_89,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v5_relat_1(X1,X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_90,plain,
    ( r1_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_45])).

cnf(c_0_91,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_75,c_0_49])).

fof(c_0_92,plain,(
    ! [X36,X37,X38] :
      ( ( v4_relat_1(X38,X36)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) )
      & ( v5_relat_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).

cnf(c_0_93,negated_conjecture,
    ( r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])])).

cnf(c_0_94,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(X1,X2,esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k2_partfun1(X1,X2,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_54]),c_0_27])])).

cnf(c_0_95,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(X2,k1_relat_1(X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_96,plain,
    ( k1_relat_1(k7_relat_1(X1,X2)) = X2
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_97,plain,
    ( X1 = k1_relat_1(X2)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ),
    inference(spm,[status(thm)],[c_0_82,c_0_84])).

cnf(c_0_98,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_71])]),c_0_87]),c_0_88])).

cnf(c_0_99,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))
    | ~ v5_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_91])).

cnf(c_0_101,plain,
    ( v5_relat_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_92])).

cnf(c_0_102,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_93])).

cnf(c_0_103,negated_conjecture,
    ( ~ v1_funct_2(k7_relat_1(esk5_0,esk4_0),esk4_0,esk3_0)
    | ~ m1_subset_1(k7_relat_1(esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_65]),c_0_54])])).

cnf(c_0_104,plain,
    ( X1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(X2,X3),X3,X1)
    | ~ v1_relat_1(X2)
    | ~ m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r1_tarski(X3,k1_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( k1_relat_1(esk5_0) = esk2_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_58]),c_0_27])]),c_0_98])).

cnf(c_0_106,plain,
    ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v5_relat_1(k7_relat_1(X1,X2),X3)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(X2,k1_relat_1(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_96]),c_0_100])).

cnf(c_0_107,negated_conjecture,
    ( v5_relat_1(k7_relat_1(esk5_0,X1),esk3_0) ),
    inference(spm,[status(thm)],[c_0_101,c_0_102])).

cnf(c_0_108,negated_conjecture,
    ( ~ m1_subset_1(k7_relat_1(esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))
    | ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_78]),c_0_105]),c_0_24])]),c_0_98])).

cnf(c_0_109,negated_conjecture,
    ( m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_107]),c_0_78]),c_0_105])])).

cnf(c_0_110,negated_conjecture,
    ( ~ m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_24])])).

cnf(c_0_111,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_27,c_0_110]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:32:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 3.94/4.14  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 3.94/4.14  # and selection function SelectMaxLComplexAvoidPosPred.
% 3.94/4.14  #
% 3.94/4.14  # Preprocessing time       : 0.028 s
% 3.94/4.14  
% 3.94/4.14  # Proof found!
% 3.94/4.14  # SZS status Theorem
% 3.94/4.14  # SZS output start CNFRefutation
% 3.94/4.14  fof(t38_funct_2, conjecture, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 3.94/4.14  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.94/4.14  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.94/4.14  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.94/4.14  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.94/4.14  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.94/4.14  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.94/4.14  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.94/4.14  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.94/4.14  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 3.94/4.14  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.94/4.14  fof(redefinition_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>k2_partfun1(X1,X2,X3,X4)=k7_relat_1(X3,X4)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 3.94/4.14  fof(t4_subset_1, axiom, ![X1]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.94/4.14  fof(t11_relset_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>((r1_tarski(k1_relat_1(X3),X1)&r1_tarski(k2_relat_1(X3),X2))=>m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.94/4.14  fof(d19_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(v5_relat_1(X2,X1)<=>r1_tarski(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.94/4.14  fof(d1_funct_2, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(((X2=k1_xboole_0=>X1=k1_xboole_0)=>(v1_funct_2(X3,X1,X2)<=>X1=k1_relset_1(X1,X2,X3)))&(X2=k1_xboole_0=>(X1=k1_xboole_0|(v1_funct_2(X3,X1,X2)<=>X3=k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.94/4.14  fof(redefinition_k1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>k1_relset_1(X1,X2,X3)=k1_relat_1(X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.94/4.14  fof(t91_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r1_tarski(X1,k1_relat_1(X2))=>k1_relat_1(k7_relat_1(X2,X1))=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.94/4.14  fof(cc2_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>(v4_relat_1(X3,X1)&v5_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.94/4.14  fof(c_0_19, negated_conjecture, ~(![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))))))), inference(assume_negation,[status(cth)],[t38_funct_2])).
% 3.94/4.14  fof(c_0_20, negated_conjecture, (((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,esk2_0,esk3_0))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0))))&(r1_tarski(esk4_0,esk2_0)&((esk3_0!=k1_xboole_0|esk2_0=k1_xboole_0)&(~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])).
% 3.94/4.14  fof(c_0_21, plain, ![X20, X21, X22]:(~r2_hidden(X20,X21)|~m1_subset_1(X21,k1_zfmisc_1(X22))|~v1_xboole_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 3.94/4.14  fof(c_0_22, plain, ![X12, X13]:((k2_zfmisc_1(X12,X13)!=k1_xboole_0|(X12=k1_xboole_0|X13=k1_xboole_0))&((X12!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0)&(X13!=k1_xboole_0|k2_zfmisc_1(X12,X13)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 3.94/4.14  fof(c_0_23, plain, ![X11]:(~r1_tarski(X11,k1_xboole_0)|X11=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 3.94/4.14  cnf(c_0_24, negated_conjecture, (r1_tarski(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.94/4.14  cnf(c_0_25, negated_conjecture, (esk2_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.94/4.14  cnf(c_0_26, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 3.94/4.14  cnf(c_0_27, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.94/4.14  cnf(c_0_28, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.94/4.14  fof(c_0_29, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 3.94/4.14  fof(c_0_30, plain, ![X15, X16]:((~m1_subset_1(X15,k1_zfmisc_1(X16))|r1_tarski(X15,X16))&(~r1_tarski(X15,X16)|m1_subset_1(X15,k1_zfmisc_1(X16)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 3.94/4.14  cnf(c_0_31, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 3.94/4.14  cnf(c_0_32, negated_conjecture, (r1_tarski(esk4_0,k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 3.94/4.14  cnf(c_0_33, negated_conjecture, (~v1_xboole_0(k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 3.94/4.14  cnf(c_0_34, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_28])).
% 3.94/4.14  cnf(c_0_35, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 3.94/4.14  fof(c_0_36, plain, ![X27, X28]:v1_relat_1(k2_zfmisc_1(X27,X28)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 3.94/4.14  cnf(c_0_37, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 3.94/4.14  cnf(c_0_38, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.94/4.14  cnf(c_0_39, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.94/4.14  fof(c_0_40, plain, ![X29, X30]:(~v1_relat_1(X30)|r1_tarski(k7_relat_1(X30,X29),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 3.94/4.14  cnf(c_0_41, negated_conjecture, (~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.94/4.14  cnf(c_0_42, negated_conjecture, (esk4_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 3.94/4.14  fof(c_0_43, plain, ![X48, X49, X50, X51]:((v1_funct_1(k2_partfun1(X48,X49,X50,X51))|(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))&(m1_subset_1(k2_partfun1(X48,X49,X50,X51),k1_zfmisc_1(k2_zfmisc_1(X48,X49)))|(~v1_funct_1(X50)|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 3.94/4.14  cnf(c_0_44, negated_conjecture, (esk3_0!=k1_xboole_0|~r2_hidden(X1,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_25]), c_0_34]), c_0_35])])).
% 3.94/4.14  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.94/4.14  cnf(c_0_46, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 3.94/4.14  cnf(c_0_47, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_37])).
% 3.94/4.14  cnf(c_0_48, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 3.94/4.14  cnf(c_0_49, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 3.94/4.14  fof(c_0_50, plain, ![X23, X24]:(~v1_relat_1(X23)|(~m1_subset_1(X24,k1_zfmisc_1(X23))|v1_relat_1(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 3.94/4.14  fof(c_0_51, plain, ![X52, X53, X54, X55]:(~v1_funct_1(X54)|~m1_subset_1(X54,k1_zfmisc_1(k2_zfmisc_1(X52,X53)))|k2_partfun1(X52,X53,X54,X55)=k7_relat_1(X54,X55)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_partfun1])])).
% 3.94/4.14  cnf(c_0_52, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0))|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_34])).
% 3.94/4.14  cnf(c_0_53, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 3.94/4.14  cnf(c_0_54, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.94/4.14  cnf(c_0_55, negated_conjecture, (r1_tarski(esk5_0,X1)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 3.94/4.14  cnf(c_0_56, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 3.94/4.14  fof(c_0_57, plain, ![X14]:m1_subset_1(k1_xboole_0,k1_zfmisc_1(X14)), inference(variable_rename,[status(thm)],[t4_subset_1])).
% 3.94/4.14  cnf(c_0_58, negated_conjecture, (v1_funct_2(esk5_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 3.94/4.14  fof(c_0_59, plain, ![X42, X43, X44]:(~v1_relat_1(X44)|(~r1_tarski(k1_relat_1(X44),X42)|~r1_tarski(k2_relat_1(X44),X43)|m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X42,X43))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_relset_1])])).
% 3.94/4.14  fof(c_0_60, plain, ![X25, X26]:((~v5_relat_1(X26,X25)|r1_tarski(k2_relat_1(X26),X25)|~v1_relat_1(X26))&(~r1_tarski(k2_relat_1(X26),X25)|v5_relat_1(X26,X25)|~v1_relat_1(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_relat_1])])])).
% 3.94/4.14  cnf(c_0_61, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 3.94/4.14  cnf(c_0_62, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_27])).
% 3.94/4.14  cnf(c_0_63, plain, (r2_hidden(X1,X2)|~v1_relat_1(X2)|~r2_hidden(X1,k7_relat_1(X2,X3))), inference(spm,[status(thm)],[c_0_38, c_0_49])).
% 3.94/4.14  cnf(c_0_64, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 3.94/4.14  cnf(c_0_65, plain, (k2_partfun1(X2,X3,X1,X4)=k7_relat_1(X1,X4)|~v1_funct_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_51])).
% 3.94/4.14  fof(c_0_66, plain, ![X45, X46, X47]:((((~v1_funct_2(X47,X45,X46)|X45=k1_relset_1(X45,X46,X47)|X46=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X45!=k1_relset_1(X45,X46,X47)|v1_funct_2(X47,X45,X46)|X46=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))&((~v1_funct_2(X47,X45,X46)|X45=k1_relset_1(X45,X46,X47)|X45!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X45!=k1_relset_1(X45,X46,X47)|v1_funct_2(X47,X45,X46)|X45!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))))&((~v1_funct_2(X47,X45,X46)|X47=k1_xboole_0|X45=k1_xboole_0|X46!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46))))&(X47!=k1_xboole_0|v1_funct_2(X47,X45,X46)|X45=k1_xboole_0|X46!=k1_xboole_0|~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(X45,X46)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).
% 3.94/4.14  fof(c_0_67, plain, ![X39, X40, X41]:(~m1_subset_1(X41,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))|k1_relset_1(X39,X40,X41)=k1_relat_1(X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).
% 3.94/4.14  cnf(c_0_68, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_54]), c_0_27])])).
% 3.94/4.14  cnf(c_0_69, negated_conjecture, (esk5_0=k1_xboole_0|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_31, c_0_55])).
% 3.94/4.14  cnf(c_0_70, plain, (k7_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_49]), c_0_56])])).
% 3.94/4.14  cnf(c_0_71, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_57])).
% 3.94/4.14  cnf(c_0_72, negated_conjecture, (v1_funct_2(esk5_0,k1_xboole_0,esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_58, c_0_25])).
% 3.94/4.14  cnf(c_0_73, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)|~r1_tarski(k2_relat_1(X1),X3)), inference(split_conjunct,[status(thm)],[c_0_59])).
% 3.94/4.14  cnf(c_0_74, plain, (r1_tarski(k2_relat_1(X1),X2)|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 3.94/4.14  cnf(c_0_75, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 3.94/4.14  cnf(c_0_76, negated_conjecture, (r1_tarski(X1,k2_zfmisc_1(esk2_0,esk3_0))|~r2_hidden(esk1_2(X1,k2_zfmisc_1(esk2_0,esk3_0)),esk5_0)), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 3.94/4.14  cnf(c_0_77, plain, (r2_hidden(esk1_2(k7_relat_1(X1,X2),X3),X1)|r1_tarski(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_63, c_0_45])).
% 3.94/4.14  cnf(c_0_78, negated_conjecture, (v1_relat_1(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_27]), c_0_46])])).
% 3.94/4.14  cnf(c_0_79, negated_conjecture, (~v1_funct_2(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_53]), c_0_54]), c_0_27])])).
% 3.94/4.14  cnf(c_0_80, plain, (k2_partfun1(X1,X2,X3,X4)=k2_partfun1(X5,X6,X3,X4)|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))), inference(spm,[status(thm)],[c_0_65, c_0_65])).
% 3.94/4.14  cnf(c_0_81, plain, (v1_funct_2(X3,X1,X2)|X2=k1_xboole_0|X1!=k1_relset_1(X1,X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.94/4.14  cnf(c_0_82, plain, (k1_relset_1(X2,X3,X1)=k1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 3.94/4.14  fof(c_0_83, plain, ![X31, X32]:(~v1_relat_1(X32)|(~r1_tarski(X31,k1_relat_1(X32))|k1_relat_1(k7_relat_1(X32,X31))=X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t91_relat_1])])).
% 3.94/4.14  cnf(c_0_84, plain, (X2=k1_relset_1(X2,X3,X1)|X3=k1_xboole_0|~v1_funct_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_66])).
% 3.94/4.14  cnf(c_0_85, negated_conjecture, (esk3_0!=k1_xboole_0|~v1_funct_2(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_xboole_0,esk3_0)|~m1_subset_1(k2_partfun1(esk2_0,esk3_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 3.94/4.14  cnf(c_0_86, plain, (k2_partfun1(X1,X2,k1_xboole_0,X3)=k1_xboole_0|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_65]), c_0_71])])).
% 3.94/4.14  cnf(c_0_87, negated_conjecture, (v1_funct_2(k1_xboole_0,k1_xboole_0,esk3_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_72, c_0_69])).
% 3.94/4.14  cnf(c_0_88, negated_conjecture, (v1_funct_1(k1_xboole_0)|esk3_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_69])).
% 3.94/4.14  cnf(c_0_89, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v5_relat_1(X1,X3)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 3.94/4.14  cnf(c_0_90, plain, (r1_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_61, c_0_45])).
% 3.94/4.14  cnf(c_0_91, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_75, c_0_49])).
% 3.94/4.14  fof(c_0_92, plain, ![X36, X37, X38]:((v4_relat_1(X38,X36)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))&(v5_relat_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relset_1])])])).
% 3.94/4.14  cnf(c_0_93, negated_conjecture, (r1_tarski(k7_relat_1(esk5_0,X1),k2_zfmisc_1(esk2_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78])])).
% 3.94/4.14  cnf(c_0_94, negated_conjecture, (~v1_funct_2(k2_partfun1(X1,X2,esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k2_partfun1(X1,X2,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_54]), c_0_27])])).
% 3.94/4.14  cnf(c_0_95, plain, (X1=k1_xboole_0|v1_funct_2(X2,k1_relat_1(X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82])])).
% 3.94/4.14  cnf(c_0_96, plain, (k1_relat_1(k7_relat_1(X1,X2))=X2|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 3.94/4.14  cnf(c_0_97, plain, (X1=k1_relat_1(X2)|X3=k1_xboole_0|~v1_funct_2(X2,X1,X3)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))), inference(spm,[status(thm)],[c_0_82, c_0_84])).
% 3.94/4.14  cnf(c_0_98, negated_conjecture, (esk3_0!=k1_xboole_0), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_71])]), c_0_87]), c_0_88])).
% 3.94/4.14  cnf(c_0_99, plain, (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X2)))|~v5_relat_1(X1,X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 3.94/4.14  cnf(c_0_100, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_64, c_0_91])).
% 3.94/4.14  cnf(c_0_101, plain, (v5_relat_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))), inference(split_conjunct,[status(thm)],[c_0_92])).
% 3.94/4.14  cnf(c_0_102, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(esk2_0,esk3_0)))), inference(spm,[status(thm)],[c_0_75, c_0_93])).
% 3.94/4.14  cnf(c_0_103, negated_conjecture, (~v1_funct_2(k7_relat_1(esk5_0,esk4_0),esk4_0,esk3_0)|~m1_subset_1(k7_relat_1(esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_65]), c_0_54])])).
% 3.94/4.14  cnf(c_0_104, plain, (X1=k1_xboole_0|v1_funct_2(k7_relat_1(X2,X3),X3,X1)|~v1_relat_1(X2)|~m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X1)))|~r1_tarski(X3,k1_relat_1(X2))), inference(spm,[status(thm)],[c_0_95, c_0_96])).
% 3.94/4.14  cnf(c_0_105, negated_conjecture, (k1_relat_1(esk5_0)=esk2_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_58]), c_0_27])]), c_0_98])).
% 3.94/4.14  cnf(c_0_106, plain, (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))|~v5_relat_1(k7_relat_1(X1,X2),X3)|~v1_relat_1(X1)|~r1_tarski(X2,k1_relat_1(X1))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_96]), c_0_100])).
% 3.94/4.14  cnf(c_0_107, negated_conjecture, (v5_relat_1(k7_relat_1(esk5_0,X1),esk3_0)), inference(spm,[status(thm)],[c_0_101, c_0_102])).
% 3.94/4.14  cnf(c_0_108, negated_conjecture, (~m1_subset_1(k7_relat_1(esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(esk4_0,esk3_0)))|~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_78]), c_0_105]), c_0_24])]), c_0_98])).
% 3.94/4.14  cnf(c_0_109, negated_conjecture, (m1_subset_1(k7_relat_1(esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,esk3_0)))|~r1_tarski(X1,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106, c_0_107]), c_0_78]), c_0_105])])).
% 3.94/4.14  cnf(c_0_110, negated_conjecture, (~m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_24])])).
% 3.94/4.14  cnf(c_0_111, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_27, c_0_110]), ['proof']).
% 3.94/4.14  # SZS output end CNFRefutation
% 3.94/4.14  # Proof object total steps             : 112
% 3.94/4.14  # Proof object clause steps            : 74
% 3.94/4.14  # Proof object formula steps           : 38
% 3.94/4.14  # Proof object conjectures             : 36
% 3.94/4.14  # Proof object clause conjectures      : 33
% 3.94/4.14  # Proof object formula conjectures     : 3
% 3.94/4.14  # Proof object initial clauses used    : 29
% 3.94/4.14  # Proof object initial formulas used   : 19
% 3.94/4.14  # Proof object generating inferences   : 42
% 3.94/4.14  # Proof object simplifying inferences  : 45
% 3.94/4.14  # Training examples: 0 positive, 0 negative
% 3.94/4.14  # Parsed axioms                        : 21
% 3.94/4.14  # Removed by relevancy pruning/SinE    : 0
% 3.94/4.14  # Initial clauses                      : 39
% 3.94/4.14  # Removed in clause preprocessing      : 0
% 3.94/4.14  # Initial clauses in saturation        : 39
% 3.94/4.14  # Processed clauses                    : 21635
% 3.94/4.14  # ...of these trivial                  : 65
% 3.94/4.14  # ...subsumed                          : 16952
% 3.94/4.14  # ...remaining for further processing  : 4618
% 3.94/4.14  # Other redundant clauses eliminated   : 11
% 3.94/4.14  # Clauses deleted for lack of memory   : 0
% 3.94/4.14  # Backward-subsumed                    : 398
% 3.94/4.14  # Backward-rewritten                   : 195
% 3.94/4.14  # Generated clauses                    : 188222
% 3.94/4.14  # ...of the previous two non-trivial   : 100211
% 3.94/4.14  # Contextual simplify-reflections      : 473
% 3.94/4.14  # Paramodulations                      : 188210
% 3.94/4.14  # Factorizations                       : 0
% 3.94/4.14  # Equation resolutions                 : 11
% 3.94/4.14  # Propositional unsat checks           : 0
% 3.94/4.14  #    Propositional check models        : 0
% 3.94/4.14  #    Propositional check unsatisfiable : 0
% 3.94/4.14  #    Propositional clauses             : 0
% 3.94/4.14  #    Propositional clauses after purity: 0
% 3.94/4.14  #    Propositional unsat core size     : 0
% 3.94/4.14  #    Propositional preprocessing time  : 0.000
% 3.94/4.14  #    Propositional encoding time       : 0.000
% 3.94/4.14  #    Propositional solver time         : 0.000
% 3.94/4.14  #    Success case prop preproc time    : 0.000
% 3.94/4.14  #    Success case prop encoding time   : 0.000
% 3.94/4.14  #    Success case prop solver time     : 0.000
% 3.94/4.14  # Current number of processed clauses  : 4017
% 3.94/4.14  #    Positive orientable unit clauses  : 146
% 3.94/4.14  #    Positive unorientable unit clauses: 0
% 3.94/4.14  #    Negative unit clauses             : 16
% 3.94/4.14  #    Non-unit-clauses                  : 3855
% 3.94/4.14  # Current number of unprocessed clauses: 77533
% 3.94/4.14  # ...number of literals in the above   : 310571
% 3.94/4.14  # Current number of archived formulas  : 0
% 3.94/4.14  # Current number of archived clauses   : 595
% 3.94/4.14  # Clause-clause subsumption calls (NU) : 1649084
% 3.94/4.14  # Rec. Clause-clause subsumption calls : 1211435
% 3.94/4.14  # Non-unit clause-clause subsumptions  : 9148
% 3.94/4.14  # Unit Clause-clause subsumption calls : 23064
% 3.94/4.14  # Rewrite failures with RHS unbound    : 0
% 3.94/4.14  # BW rewrite match attempts            : 775
% 3.94/4.14  # BW rewrite match successes           : 17
% 3.94/4.14  # Condensation attempts                : 0
% 3.94/4.14  # Condensation successes               : 0
% 3.94/4.14  # Termbank termtop insertions          : 3256389
% 3.94/4.14  
% 3.94/4.14  # -------------------------------------------------
% 3.94/4.14  # User time                : 3.724 s
% 3.94/4.14  # System time              : 0.068 s
% 3.94/4.14  # Total time               : 3.792 s
% 3.94/4.14  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
