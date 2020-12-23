%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:10 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 237 expanded)
%              Number of clauses        :   65 ( 113 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  256 ( 742 expanded)
%              Number of equality atoms :  137 ( 413 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t12_setfam_1,axiom,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(t18_funct_1,conjecture,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(t15_funct_1,axiom,(
    ! [X1] :
      ( X1 != k1_xboole_0
     => ! [X2] :
        ? [X3] :
          ( v1_relat_1(X3)
          & v1_funct_1(X3)
          & k1_relat_1(X3) = X1
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(dt_k6_relat_1,axiom,(
    ! [X1] : v1_relat_1(k6_relat_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t81_relat_1,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(c_0_16,plain,(
    ! [X33,X34] : ~ r2_hidden(X33,k2_zfmisc_1(X33,X34)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

fof(c_0_17,plain,(
    ! [X31,X32] :
      ( ( k2_zfmisc_1(X31,X32) != k1_xboole_0
        | X31 = k1_xboole_0
        | X32 = k1_xboole_0 )
      & ( X31 != k1_xboole_0
        | k2_zfmisc_1(X31,X32) = k1_xboole_0 )
      & ( X32 != k1_xboole_0
        | k2_zfmisc_1(X31,X32) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X22,X23,X24,X25,X26,X27] :
      ( ( ~ r2_hidden(X24,X23)
        | X24 = X22
        | X23 != k1_tarski(X22) )
      & ( X25 != X22
        | r2_hidden(X25,X23)
        | X23 != k1_tarski(X22) )
      & ( ~ r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) != X26
        | X27 = k1_tarski(X26) )
      & ( r2_hidden(esk3_2(X26,X27),X27)
        | esk3_2(X26,X27) = X26
        | X27 = k1_tarski(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X35,X36] : k1_setfam_1(k2_tarski(X35,X36)) = k3_xboole_0(X35,X36) ),
    inference(variable_rename,[status(thm)],[t12_setfam_1])).

fof(c_0_22,plain,(
    ! [X29,X30] : k1_enumset1(X29,X29,X30) = k2_tarski(X29,X30) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_23,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14,X15,X16,X17,X18] :
      ( ( r2_hidden(X14,X11)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( r2_hidden(X14,X12)
        | ~ r2_hidden(X14,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X15,X11)
        | ~ r2_hidden(X15,X12)
        | r2_hidden(X15,X13)
        | X13 != k3_xboole_0(X11,X12) )
      & ( ~ r2_hidden(esk2_3(X16,X17,X18),X18)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X16)
        | ~ r2_hidden(esk2_3(X16,X17,X18),X17)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X16)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_3(X16,X17,X18),X17)
        | r2_hidden(esk2_3(X16,X17,X18),X18)
        | X18 = k3_xboole_0(X16,X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_28,plain,(
    ! [X20] : k3_xboole_0(X20,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_29,plain,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0
    | X2 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_33,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk3_2(X1,X2),X2)
    | esk3_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( esk3_2(X1,k1_xboole_0) = X1
    | k1_tarski(X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_29])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1,X2] :
        ~ ( ~ ( X1 = k1_xboole_0
              & X2 != k1_xboole_0 )
          & ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ~ ( X2 = k1_relat_1(X3)
                  & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_funct_1])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X4,X4,X2))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_37,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_32,c_0_31])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_23])).

fof(c_0_39,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_40,negated_conjecture,(
    ! [X47] :
      ( ( esk6_0 != k1_xboole_0
        | esk7_0 = k1_xboole_0 )
      & ( ~ v1_relat_1(X47)
        | ~ v1_funct_1(X47)
        | esk7_0 != k1_relat_1(X47)
        | ~ r1_tarski(k2_relat_1(X47),esk6_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])])).

cnf(c_0_41,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | esk7_0 != k1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_45,plain,(
    ! [X39,X41] :
      ( v1_relat_1(esk4_1(X39))
      & v1_funct_1(esk4_1(X39))
      & k1_relat_1(esk4_1(X39)) = X39
      & ( ~ r2_hidden(X41,X39)
        | k1_funct_1(esk4_1(X39),X41) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_46,plain,(
    ! [X38] :
      ( ( k1_relat_1(X38) != k1_xboole_0
        | X38 = k1_xboole_0
        | ~ v1_relat_1(X38) )
      & ( k2_relat_1(X38) != k1_xboole_0
        | X38 = k1_xboole_0
        | ~ v1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_47,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X1)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_48,plain,(
    ! [X42,X43] :
      ( ( v1_relat_1(esk5_2(X42,X43))
        | X42 = k1_xboole_0 )
      & ( v1_funct_1(esk5_2(X42,X43))
        | X42 = k1_xboole_0 )
      & ( k1_relat_1(esk5_2(X42,X43)) = X42
        | X42 = k1_xboole_0 )
      & ( k2_relat_1(esk5_2(X42,X43)) = k1_tarski(X43)
        | X42 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(X1) != esk7_0
    | k2_relat_1(X1) != k1_xboole_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_50,plain,
    ( v1_funct_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( k1_relat_1(esk4_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,plain,
    ( v1_relat_1(esk4_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_54,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_55,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X1) ),
    inference(rw,[status(thm)],[c_0_47,c_0_31])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_57,plain,
    ( k2_relat_1(esk5_2(X1,X2)) = k1_tarski(X2)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,plain,
    ( v1_relat_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_59,plain,
    ( v1_funct_1(esk5_2(X1,X2))
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_60,negated_conjecture,
    ( k2_relat_1(esk4_1(X1)) != k1_xboole_0
    | X1 != esk7_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_61,plain,
    ( esk4_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_52])])).

cnf(c_0_62,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_63,plain,
    ( esk1_2(X1,X2) = X3
    | r1_tarski(X1,X2)
    | X1 != k1_tarski(X3) ),
    inference(spm,[status(thm)],[c_0_54,c_0_42])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_65,plain,
    ( X1 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X2))
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)
    | X3 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_55])).

cnf(c_0_66,plain,
    ( X3 = k1_setfam_1(k1_enumset1(X1,X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_56,c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( X1 = k1_xboole_0
    | k1_relat_1(esk5_2(X1,X2)) != esk7_0
    | ~ r1_tarski(k1_tarski(X2),esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_57]),c_0_58]),c_0_59])).

cnf(c_0_68,plain,
    ( k1_relat_1(esk5_2(X1,X2)) = X1
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_69,negated_conjecture,
    ( X1 != esk7_0
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_70,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_71,plain,
    ( esk1_2(k1_tarski(X1),X2) = X1
    | r1_tarski(k1_tarski(X1),X2) ),
    inference(er,[status(thm)],[c_0_63])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,X2)
    | X3 != k1_setfam_1(k1_enumset1(X2,X2,X4))
    | ~ r2_hidden(X1,X3) ),
    inference(rw,[status(thm)],[c_0_64,c_0_31])).

cnf(c_0_73,plain,
    ( X1 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X2))
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(er,[status(thm)],[c_0_65])).

cnf(c_0_74,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1)
    | X3 != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_66]),c_0_37])).

fof(c_0_75,plain,(
    ! [X37] : v1_relat_1(k6_relat_1(X37)) ),
    inference(variable_rename,[status(thm)],[dt_k6_relat_1])).

cnf(c_0_76,negated_conjecture,
    ( X1 != esk7_0
    | ~ r1_tarski(k1_tarski(X2),esk6_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_77,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_78,plain,
    ( r2_hidden(esk2_3(k1_xboole_0,X1,X2),X2)
    | ~ r2_hidden(X3,X2) ),
    inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_38])])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1) ),
    inference(er,[status(thm)],[c_0_74])).

fof(c_0_80,plain,(
    ! [X21] : r1_tarski(k1_xboole_0,X21) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_81,plain,
    ( v1_relat_1(k6_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_82,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t81_relat_1])).

cnf(c_0_83,negated_conjecture,
    ( X1 != esk7_0
    | ~ r2_hidden(X2,esk6_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_85,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_86,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_87,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_88,plain,
    ( v1_funct_1(k1_xboole_0)
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_61])).

cnf(c_0_89,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | X1 != esk7_0 ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_90,negated_conjecture,
    ( esk7_0 != k1_xboole_0
    | ~ v1_funct_1(k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_62]),c_0_85]),c_0_86])]),c_0_87])])).

cnf(c_0_91,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_88])).

cnf(c_0_92,negated_conjecture,
    ( esk7_0 = k1_xboole_0
    | esk6_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_93,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_89])).

cnf(c_0_94,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90,c_0_91])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92,c_0_93])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:25:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.38  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.12/0.38  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.12/0.38  #
% 0.12/0.38  # Preprocessing time       : 0.029 s
% 0.12/0.38  
% 0.12/0.38  # Proof found!
% 0.12/0.38  # SZS status Theorem
% 0.12/0.38  # SZS output start CNFRefutation
% 0.12/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.12/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.38  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.12/0.38  fof(t12_setfam_1, axiom, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.12/0.38  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.12/0.38  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.12/0.38  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 0.12/0.38  fof(t18_funct_1, conjecture, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 0.12/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.38  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.12/0.38  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 0.12/0.38  fof(t15_funct_1, axiom, ![X1]:(X1!=k1_xboole_0=>![X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&k2_relat_1(X3)=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 0.12/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.38  fof(dt_k6_relat_1, axiom, ![X1]:v1_relat_1(k6_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 0.12/0.38  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.12/0.38  fof(t81_relat_1, axiom, k6_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 0.12/0.38  fof(c_0_16, plain, ![X33, X34]:~r2_hidden(X33,k2_zfmisc_1(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.12/0.38  fof(c_0_17, plain, ![X31, X32]:((k2_zfmisc_1(X31,X32)!=k1_xboole_0|(X31=k1_xboole_0|X32=k1_xboole_0))&((X31!=k1_xboole_0|k2_zfmisc_1(X31,X32)=k1_xboole_0)&(X32!=k1_xboole_0|k2_zfmisc_1(X31,X32)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.38  cnf(c_0_18, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.38  cnf(c_0_19, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.38  fof(c_0_20, plain, ![X22, X23, X24, X25, X26, X27]:(((~r2_hidden(X24,X23)|X24=X22|X23!=k1_tarski(X22))&(X25!=X22|r2_hidden(X25,X23)|X23!=k1_tarski(X22)))&((~r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)!=X26|X27=k1_tarski(X26))&(r2_hidden(esk3_2(X26,X27),X27)|esk3_2(X26,X27)=X26|X27=k1_tarski(X26)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.12/0.38  fof(c_0_21, plain, ![X35, X36]:k1_setfam_1(k2_tarski(X35,X36))=k3_xboole_0(X35,X36), inference(variable_rename,[status(thm)],[t12_setfam_1])).
% 0.12/0.38  fof(c_0_22, plain, ![X29, X30]:k1_enumset1(X29,X29,X30)=k2_tarski(X29,X30), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.12/0.38  cnf(c_0_23, plain, (X1!=k1_xboole_0|~r2_hidden(X2,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.12/0.38  cnf(c_0_24, plain, (r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  fof(c_0_25, plain, ![X11, X12, X13, X14, X15, X16, X17, X18]:((((r2_hidden(X14,X11)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12))&(r2_hidden(X14,X12)|~r2_hidden(X14,X13)|X13!=k3_xboole_0(X11,X12)))&(~r2_hidden(X15,X11)|~r2_hidden(X15,X12)|r2_hidden(X15,X13)|X13!=k3_xboole_0(X11,X12)))&((~r2_hidden(esk2_3(X16,X17,X18),X18)|(~r2_hidden(esk2_3(X16,X17,X18),X16)|~r2_hidden(esk2_3(X16,X17,X18),X17))|X18=k3_xboole_0(X16,X17))&((r2_hidden(esk2_3(X16,X17,X18),X16)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))&(r2_hidden(esk2_3(X16,X17,X18),X17)|r2_hidden(esk2_3(X16,X17,X18),X18)|X18=k3_xboole_0(X16,X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.12/0.38  cnf(c_0_26, plain, (k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.38  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.12/0.38  fof(c_0_28, plain, ![X20]:k3_xboole_0(X20,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.12/0.38  cnf(c_0_29, plain, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0|X2!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.38  cnf(c_0_30, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_31, plain, (k1_setfam_1(k1_enumset1(X1,X1,X2))=k3_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.38  cnf(c_0_32, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.38  cnf(c_0_33, plain, (X2=k1_tarski(X1)|~r2_hidden(esk3_2(X1,X2),X2)|esk3_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_34, plain, (esk3_2(X1,k1_xboole_0)=X1|k1_tarski(X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_29])).
% 0.12/0.38  fof(c_0_35, negated_conjecture, ~(![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1))))))), inference(assume_negation,[status(cth)],[t18_funct_1])).
% 0.12/0.38  cnf(c_0_36, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X4,X4,X2))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.38  cnf(c_0_37, plain, (k1_setfam_1(k1_enumset1(X1,X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_32, c_0_31])).
% 0.12/0.38  cnf(c_0_38, plain, (~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_23])).
% 0.12/0.38  fof(c_0_39, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.38  fof(c_0_40, negated_conjecture, ![X47]:((esk6_0!=k1_xboole_0|esk7_0=k1_xboole_0)&(~v1_relat_1(X47)|~v1_funct_1(X47)|(esk7_0!=k1_relat_1(X47)|~r1_tarski(k2_relat_1(X47),esk6_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])])).
% 0.12/0.38  cnf(c_0_41, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.12/0.38  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_43, negated_conjecture, (~v1_relat_1(X1)|~v1_funct_1(X1)|esk7_0!=k1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_44, plain, (r1_tarski(X1,X2)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.12/0.38  fof(c_0_45, plain, ![X39, X41]:(((v1_relat_1(esk4_1(X39))&v1_funct_1(esk4_1(X39)))&k1_relat_1(esk4_1(X39))=X39)&(~r2_hidden(X41,X39)|k1_funct_1(esk4_1(X39),X41)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.12/0.38  fof(c_0_46, plain, ![X38]:((k1_relat_1(X38)!=k1_xboole_0|X38=k1_xboole_0|~v1_relat_1(X38))&(k2_relat_1(X38)!=k1_xboole_0|X38=k1_xboole_0|~v1_relat_1(X38))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.12/0.38  cnf(c_0_47, plain, (r2_hidden(esk2_3(X1,X2,X3),X1)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  fof(c_0_48, plain, ![X42, X43]:((((v1_relat_1(esk5_2(X42,X43))|X42=k1_xboole_0)&(v1_funct_1(esk5_2(X42,X43))|X42=k1_xboole_0))&(k1_relat_1(esk5_2(X42,X43))=X42|X42=k1_xboole_0))&(k2_relat_1(esk5_2(X42,X43))=k1_tarski(X43)|X42=k1_xboole_0)), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_funct_1])])])])])).
% 0.12/0.38  cnf(c_0_49, negated_conjecture, (k1_relat_1(X1)!=esk7_0|k2_relat_1(X1)!=k1_xboole_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.12/0.38  cnf(c_0_50, plain, (v1_funct_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.38  cnf(c_0_51, plain, (k1_relat_1(esk4_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.38  cnf(c_0_52, plain, (v1_relat_1(esk4_1(X1))), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.12/0.38  cnf(c_0_53, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.12/0.38  cnf(c_0_54, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.38  cnf(c_0_55, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X1)), inference(rw,[status(thm)],[c_0_47, c_0_31])).
% 0.12/0.38  cnf(c_0_56, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_57, plain, (k2_relat_1(esk5_2(X1,X2))=k1_tarski(X2)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_58, plain, (v1_relat_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_59, plain, (v1_funct_1(esk5_2(X1,X2))|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_60, negated_conjecture, (k2_relat_1(esk4_1(X1))!=k1_xboole_0|X1!=esk7_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51]), c_0_52])])).
% 0.12/0.38  cnf(c_0_61, plain, (esk4_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_51]), c_0_52])])).
% 0.12/0.38  cnf(c_0_62, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.38  cnf(c_0_63, plain, (esk1_2(X1,X2)=X3|r1_tarski(X1,X2)|X1!=k1_tarski(X3)), inference(spm,[status(thm)],[c_0_54, c_0_42])).
% 0.12/0.38  cnf(c_0_64, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.38  cnf(c_0_65, plain, (X1=k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X2))|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)|X3!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_55])).
% 0.12/0.38  cnf(c_0_66, plain, (X3=k1_setfam_1(k1_enumset1(X1,X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_56, c_0_31])).
% 0.12/0.38  cnf(c_0_67, negated_conjecture, (X1=k1_xboole_0|k1_relat_1(esk5_2(X1,X2))!=esk7_0|~r1_tarski(k1_tarski(X2),esk6_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_57]), c_0_58]), c_0_59])).
% 0.12/0.38  cnf(c_0_68, plain, (k1_relat_1(esk5_2(X1,X2))=X1|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.38  cnf(c_0_69, negated_conjecture, (X1!=esk7_0|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_61]), c_0_62])])).
% 0.12/0.38  cnf(c_0_70, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.12/0.38  cnf(c_0_71, plain, (esk1_2(k1_tarski(X1),X2)=X1|r1_tarski(k1_tarski(X1),X2)), inference(er,[status(thm)],[c_0_63])).
% 0.12/0.38  cnf(c_0_72, plain, (r2_hidden(X1,X2)|X3!=k1_setfam_1(k1_enumset1(X2,X2,X4))|~r2_hidden(X1,X3)), inference(rw,[status(thm)],[c_0_64, c_0_31])).
% 0.12/0.38  cnf(c_0_73, plain, (X1=k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X2))|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(er,[status(thm)],[c_0_65])).
% 0.12/0.38  cnf(c_0_74, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1)|X3!=k1_xboole_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_66]), c_0_37])).
% 0.12/0.38  fof(c_0_75, plain, ![X37]:v1_relat_1(k6_relat_1(X37)), inference(variable_rename,[status(thm)],[dt_k6_relat_1])).
% 0.12/0.38  cnf(c_0_76, negated_conjecture, (X1!=esk7_0|~r1_tarski(k1_tarski(X2),esk6_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_68]), c_0_69])).
% 0.12/0.38  cnf(c_0_77, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.12/0.38  cnf(c_0_78, plain, (r2_hidden(esk2_3(k1_xboole_0,X1,X2),X2)|~r2_hidden(X3,X2)), inference(er,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_38])])).
% 0.12/0.38  cnf(c_0_79, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1)), inference(er,[status(thm)],[c_0_74])).
% 0.12/0.38  fof(c_0_80, plain, ![X21]:r1_tarski(k1_xboole_0,X21), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.12/0.38  cnf(c_0_81, plain, (v1_relat_1(k6_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_75])).
% 0.12/0.38  cnf(c_0_82, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t81_relat_1])).
% 0.12/0.38  cnf(c_0_83, negated_conjecture, (X1!=esk7_0|~r2_hidden(X2,esk6_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.12/0.38  cnf(c_0_84, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(k1_xboole_0,X2,X1),X1)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.12/0.38  cnf(c_0_85, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.38  cnf(c_0_86, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.12/0.38  cnf(c_0_87, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_81, c_0_82])).
% 0.12/0.38  cnf(c_0_88, plain, (v1_funct_1(k1_xboole_0)|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_61])).
% 0.12/0.38  cnf(c_0_89, negated_conjecture, (esk6_0=k1_xboole_0|X1!=esk7_0), inference(spm,[status(thm)],[c_0_83, c_0_84])).
% 0.12/0.38  cnf(c_0_90, negated_conjecture, (esk7_0!=k1_xboole_0|~v1_funct_1(k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_62]), c_0_85]), c_0_86])]), c_0_87])])).
% 0.12/0.38  cnf(c_0_91, plain, (v1_funct_1(k1_xboole_0)), inference(er,[status(thm)],[c_0_88])).
% 0.12/0.38  cnf(c_0_92, negated_conjecture, (esk7_0=k1_xboole_0|esk6_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.12/0.38  cnf(c_0_93, negated_conjecture, (esk6_0=k1_xboole_0), inference(er,[status(thm)],[c_0_89])).
% 0.12/0.38  cnf(c_0_94, negated_conjecture, (esk7_0!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_90, c_0_91])])).
% 0.12/0.38  cnf(c_0_95, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_92, c_0_93])]), c_0_94]), ['proof']).
% 0.12/0.38  # SZS output end CNFRefutation
% 0.12/0.38  # Proof object total steps             : 96
% 0.12/0.38  # Proof object clause steps            : 65
% 0.12/0.38  # Proof object formula steps           : 31
% 0.12/0.38  # Proof object conjectures             : 16
% 0.12/0.38  # Proof object clause conjectures      : 13
% 0.12/0.38  # Proof object formula conjectures     : 3
% 0.12/0.38  # Proof object initial clauses used    : 29
% 0.12/0.38  # Proof object initial formulas used   : 16
% 0.12/0.38  # Proof object generating inferences   : 28
% 0.12/0.38  # Proof object simplifying inferences  : 31
% 0.12/0.38  # Training examples: 0 positive, 0 negative
% 0.12/0.38  # Parsed axioms                        : 16
% 0.12/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.38  # Initial clauses                      : 37
% 0.12/0.38  # Removed in clause preprocessing      : 2
% 0.12/0.38  # Initial clauses in saturation        : 35
% 0.12/0.38  # Processed clauses                    : 116
% 0.12/0.38  # ...of these trivial                  : 2
% 0.12/0.38  # ...subsumed                          : 27
% 0.12/0.38  # ...remaining for further processing  : 87
% 0.12/0.38  # Other redundant clauses eliminated   : 17
% 0.12/0.38  # Clauses deleted for lack of memory   : 0
% 0.12/0.38  # Backward-subsumed                    : 6
% 0.12/0.38  # Backward-rewritten                   : 7
% 0.12/0.38  # Generated clauses                    : 429
% 0.12/0.38  # ...of the previous two non-trivial   : 379
% 0.12/0.38  # Contextual simplify-reflections      : 5
% 0.12/0.38  # Paramodulations                      : 380
% 0.12/0.38  # Factorizations                       : 15
% 0.12/0.38  # Equation resolutions                 : 33
% 0.12/0.38  # Propositional unsat checks           : 0
% 0.12/0.38  #    Propositional check models        : 0
% 0.12/0.38  #    Propositional check unsatisfiable : 0
% 0.12/0.38  #    Propositional clauses             : 0
% 0.12/0.38  #    Propositional clauses after purity: 0
% 0.12/0.38  #    Propositional unsat core size     : 0
% 0.12/0.38  #    Propositional preprocessing time  : 0.000
% 0.12/0.38  #    Propositional encoding time       : 0.000
% 0.12/0.38  #    Propositional solver time         : 0.000
% 0.12/0.38  #    Success case prop preproc time    : 0.000
% 0.12/0.38  #    Success case prop encoding time   : 0.000
% 0.12/0.38  #    Success case prop solver time     : 0.000
% 0.12/0.38  # Current number of processed clauses  : 72
% 0.12/0.38  #    Positive orientable unit clauses  : 16
% 0.12/0.38  #    Positive unorientable unit clauses: 0
% 0.12/0.38  #    Negative unit clauses             : 4
% 0.12/0.38  #    Non-unit-clauses                  : 52
% 0.12/0.38  # Current number of unprocessed clauses: 295
% 0.12/0.38  # ...number of literals in the above   : 1157
% 0.12/0.38  # Current number of archived formulas  : 0
% 0.12/0.38  # Current number of archived clauses   : 16
% 0.12/0.38  # Clause-clause subsumption calls (NU) : 337
% 0.12/0.38  # Rec. Clause-clause subsumption calls : 264
% 0.12/0.38  # Non-unit clause-clause subsumptions  : 24
% 0.12/0.38  # Unit Clause-clause subsumption calls : 23
% 0.12/0.38  # Rewrite failures with RHS unbound    : 0
% 0.12/0.38  # BW rewrite match attempts            : 7
% 0.12/0.38  # BW rewrite match successes           : 3
% 0.12/0.38  # Condensation attempts                : 0
% 0.12/0.38  # Condensation successes               : 0
% 0.12/0.38  # Termbank termtop insertions          : 6527
% 0.12/0.38  
% 0.12/0.38  # -------------------------------------------------
% 0.12/0.38  # User time                : 0.040 s
% 0.12/0.38  # System time              : 0.004 s
% 0.12/0.38  # Total time               : 0.044 s
% 0.12/0.38  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
