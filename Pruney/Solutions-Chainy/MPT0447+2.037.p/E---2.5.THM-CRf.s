%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:27 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 383 expanded)
%              Number of clauses        :   78 ( 182 expanded)
%              Number of leaves         :   19 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  309 ( 933 expanded)
%              Number of equality atoms :   74 ( 252 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2)
        & ! [X4] :
            ( ( r1_tarski(X1,X4)
              & r1_tarski(X3,X4) )
           => r1_tarski(X2,X4) ) )
     => X2 = k2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t31_relat_1,conjecture,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(t43_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,k2_xboole_0(X2,X3))
     => r1_tarski(k4_xboole_0(X1,X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t8_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X2) )
     => r1_tarski(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(t44_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X1,X2),X3)
     => r1_tarski(X1,k2_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(t10_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => r1_tarski(X1,k2_xboole_0(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(t26_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

fof(t15_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_relat_1)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_19,plain,(
    ! [X16,X17,X18] :
      ( ( r1_tarski(X16,esk3_3(X16,X17,X18))
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X18,X17)
        | X17 = k2_xboole_0(X16,X18) )
      & ( r1_tarski(X18,esk3_3(X16,X17,X18))
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X18,X17)
        | X17 = k2_xboole_0(X16,X18) )
      & ( ~ r1_tarski(X17,esk3_3(X16,X17,X18))
        | ~ r1_tarski(X16,X17)
        | ~ r1_tarski(X18,X17)
        | X17 = k2_xboole_0(X16,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).

fof(c_0_20,plain,(
    ! [X43,X44] : k3_tarski(k2_tarski(X43,X44)) = k2_xboole_0(X43,X44) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k3_relat_1(X1),k3_relat_1(X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t31_relat_1])).

fof(c_0_22,plain,(
    ! [X21,X22,X23] :
      ( ~ r1_tarski(X21,k2_xboole_0(X22,X23))
      | r1_tarski(k4_xboole_0(X21,X22),X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).

fof(c_0_23,plain,(
    ! [X11,X12] :
      ( ( r1_tarski(X11,X12)
        | X11 != X12 )
      & ( r1_tarski(X12,X11)
        | X11 != X12 )
      & ( ~ r1_tarski(X11,X12)
        | ~ r1_tarski(X12,X11)
        | X11 = X12 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,esk3_3(X2,X3,X1))
    | X3 = k2_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_26,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & v1_relat_1(esk11_0)
    & r1_tarski(esk10_0,esk11_0)
    & ~ r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).

fof(c_0_27,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

fof(c_0_28,plain,(
    ! [X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( r2_hidden(X34,esk4_3(X32,X33,X34))
        | ~ r2_hidden(X34,X33)
        | X33 != k3_tarski(X32) )
      & ( r2_hidden(esk4_3(X32,X33,X34),X32)
        | ~ r2_hidden(X34,X33)
        | X33 != k3_tarski(X32) )
      & ( ~ r2_hidden(X36,X37)
        | ~ r2_hidden(X37,X32)
        | r2_hidden(X36,X33)
        | X33 != k3_tarski(X32) )
      & ( ~ r2_hidden(esk5_2(X38,X39),X39)
        | ~ r2_hidden(esk5_2(X38,X39),X41)
        | ~ r2_hidden(X41,X38)
        | X39 = k3_tarski(X38) )
      & ( r2_hidden(esk5_2(X38,X39),esk6_2(X38,X39))
        | r2_hidden(esk5_2(X38,X39),X39)
        | X39 = k3_tarski(X38) )
      & ( r2_hidden(esk6_2(X38,X39),X38)
        | r2_hidden(esk5_2(X38,X39),X39)
        | X39 = k3_tarski(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( X3 = k3_tarski(k2_tarski(X2,X1))
    | r1_tarski(X1,esk3_3(X2,X3,X1))
    | ~ r1_tarski(X2,X3)
    | ~ r1_tarski(X1,X3) ),
    inference(rw,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(esk10_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk4_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | X2 != k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_35,plain,(
    ! [X9] :
      ( X9 = k1_xboole_0
      | r2_hidden(esk2_1(X9),X9) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

fof(c_0_36,plain,(
    ! [X29,X30,X31] :
      ( ~ r1_tarski(X29,X30)
      | ~ r1_tarski(X31,X30)
      | r1_tarski(k2_xboole_0(X29,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).

cnf(c_0_37,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_25])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( k3_tarski(k2_tarski(esk10_0,X1)) = esk11_0
    | r1_tarski(X1,esk3_3(esk10_0,esk11_0,X1))
    | ~ r1_tarski(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

fof(c_0_40,plain,(
    ! [X47,X48,X49,X51,X52,X53,X54,X56] :
      ( ( ~ r2_hidden(X49,X48)
        | r2_hidden(k4_tarski(X49,esk7_3(X47,X48,X49)),X47)
        | X48 != k1_relat_1(X47) )
      & ( ~ r2_hidden(k4_tarski(X51,X52),X47)
        | r2_hidden(X51,X48)
        | X48 != k1_relat_1(X47) )
      & ( ~ r2_hidden(esk8_2(X53,X54),X54)
        | ~ r2_hidden(k4_tarski(esk8_2(X53,X54),X56),X53)
        | X54 = k1_relat_1(X53) )
      & ( r2_hidden(esk8_2(X53,X54),X54)
        | r2_hidden(k4_tarski(esk8_2(X53,X54),esk9_2(X53,X54)),X53)
        | X54 = k1_relat_1(X53) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_41,plain,
    ( X1 != k3_tarski(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

fof(c_0_43,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

fof(c_0_44,plain,(
    ! [X58] :
      ( ~ v1_relat_1(X58)
      | k3_relat_1(X58) = k2_xboole_0(k1_relat_1(X58),k2_relat_1(X58)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_45,plain,
    ( r1_tarski(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_46,plain,(
    ! [X24,X25,X26] :
      ( ~ r1_tarski(k4_xboole_0(X24,X25),X26)
      | r1_tarski(X24,k2_xboole_0(X25,X26)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).

cnf(c_0_47,plain,
    ( X1 = k2_xboole_0(X2,X3)
    | ~ r1_tarski(X1,esk3_3(X2,X1,X3))
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_48,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1),X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_49,negated_conjecture,
    ( k3_tarski(k2_tarski(esk10_0,esk11_0)) = esk11_0
    | r1_tarski(esk11_0,esk3_3(esk10_0,esk11_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

cnf(c_0_50,plain,
    ( r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | X1 != k3_tarski(X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

fof(c_0_54,plain,(
    ! [X13,X14,X15] :
      ( ~ r1_tarski(X13,X14)
      | r1_tarski(X13,k2_xboole_0(X15,X14)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).

fof(c_0_55,plain,(
    ! [X61,X62] :
      ( ~ v1_relat_1(X61)
      | ~ v1_relat_1(X62)
      | k2_relat_1(k2_xboole_0(X61,X62)) = k2_xboole_0(k2_relat_1(X61),k2_relat_1(X62)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)
    | ~ r1_tarski(X3,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_45,c_0_25])).

cnf(c_0_58,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,plain,
    ( X1 = k3_tarski(k2_tarski(X2,X3))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X1,esk3_3(X2,X1,X3)) ),
    inference(rw,[status(thm)],[c_0_47,c_0_25])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk11_0,esk3_3(esk10_0,esk11_0,esk11_0))
    | r1_tarski(k4_xboole_0(esk11_0,esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

fof(c_0_61,plain,(
    ! [X59,X60] :
      ( ~ v1_relat_1(X59)
      | ~ v1_relat_1(X60)
      | r1_tarski(k6_subset_1(k1_relat_1(X59),k1_relat_1(X60)),k1_relat_1(k6_subset_1(X59,X60))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).

fof(c_0_62,plain,(
    ! [X45,X46] : k6_subset_1(X45,X46) = k4_xboole_0(X45,X46) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

cnf(c_0_63,plain,
    ( X1 != k1_relat_1(X2)
    | ~ r2_hidden(X3,X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_50])).

cnf(c_0_64,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_65,plain,
    ( k3_tarski(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_66,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_67,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X1,X2))) ),
    inference(rw,[status(thm)],[c_0_52,c_0_25])).

cnf(c_0_68,plain,
    ( k3_relat_1(X1) = k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_53,c_0_25])).

cnf(c_0_69,plain,
    ( r1_tarski(X1,k2_xboole_0(X3,X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_70,plain,
    ( k2_relat_1(k2_xboole_0(X1,X2)) = k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_71,plain,
    ( X1 = k3_tarski(k2_tarski(X2,X3))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(rw,[status(thm)],[c_0_58,c_0_25])).

cnf(c_0_73,negated_conjecture,
    ( k3_tarski(k2_tarski(esk10_0,esk11_0)) = esk11_0
    | r1_tarski(k4_xboole_0(esk11_0,esk10_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_38]),c_0_32])])).

cnf(c_0_74,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_75,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_76,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_relat_1(X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_63,c_0_42])).

cnf(c_0_77,plain,
    ( v1_xboole_0(X1)
    | X1 != k3_tarski(X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_64])).

cnf(c_0_78,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

fof(c_0_79,plain,(
    ! [X20] : r1_tarski(k1_xboole_0,X20) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_80,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(k3_tarski(k2_tarski(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_67])).

cnf(c_0_81,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_82,plain,
    ( r1_tarski(k3_relat_1(X1),X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k2_relat_1(X1),X2)
    | ~ r1_tarski(k1_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_68])).

cnf(c_0_83,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_84,plain,
    ( r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))
    | ~ r1_tarski(X1,X2) ),
    inference(rw,[status(thm)],[c_0_69,c_0_25])).

cnf(c_0_85,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70,c_0_25]),c_0_25])).

cnf(c_0_86,plain,
    ( X1 = k3_tarski(k2_tarski(X2,X3))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X3)
    | ~ r1_tarski(X3,X1)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(k4_xboole_0(esk11_0,esk10_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_73])).

cnf(c_0_88,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75]),c_0_75])).

cnf(c_0_89,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(er,[status(thm)],[c_0_76])).

cnf(c_0_90,plain,
    ( v1_xboole_0(X1)
    | X1 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_66])])).

cnf(c_0_91,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_92,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = X1
    | ~ r1_tarski(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_57]),c_0_38])])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))
    | ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_83])])).

cnf(c_0_94,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_68])).

cnf(c_0_95,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_96,plain,
    ( r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k2_tarski(X1,X2))))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_85])).

cnf(c_0_97,negated_conjecture,
    ( k3_tarski(k2_tarski(esk10_0,esk11_0)) = esk11_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_87]),c_0_38]),c_0_32])])).

cnf(c_0_98,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_relat_1(k4_xboole_0(X1,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_88])).

cnf(c_0_99,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_100,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_91])).

cnf(c_0_101,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3),X4)
    | ~ r1_tarski(X2,k3_tarski(k2_tarski(X3,X4)))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,X4))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_57])).

cnf(c_0_102,plain,
    ( r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3)
    | ~ r1_tarski(X3,X2) ),
    inference(spm,[status(thm)],[c_0_84,c_0_92])).

cnf(c_0_103,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))
    | ~ r1_tarski(k2_relat_1(esk10_0),k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_95])])).

cnf(c_0_104,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk10_0),k2_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_95]),c_0_83])])).

cnf(c_0_105,plain,
    ( r1_tarski(X1,k3_relat_1(X2))
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_68])).

cnf(c_0_106,plain,
    ( k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)) = k1_xboole_0
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_99]),c_0_91])])).

cnf(c_0_107,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3) = k1_xboole_0
    | ~ r1_tarski(X2,k3_tarski(k2_tarski(X3,k1_xboole_0)))
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X3,k1_xboole_0))) ),
    inference(spm,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_108,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | ~ r1_tarski(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_102,c_0_32])).

cnf(c_0_109,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_104])])).

cnf(c_0_110,plain,
    ( r1_tarski(k1_relat_1(X1),k3_relat_1(X2))
    | k4_xboole_0(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_91])])).

cnf(c_0_111,plain,
    ( k4_xboole_0(X1,X2) = k1_xboole_0
    | ~ r1_tarski(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)))
    | ~ r1_tarski(X3,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_92]),c_0_102])).

cnf(c_0_112,negated_conjecture,
    ( r1_tarski(esk10_0,k3_tarski(k2_tarski(esk11_0,X1))) ),
    inference(spm,[status(thm)],[c_0_108,c_0_67])).

cnf(c_0_113,negated_conjecture,
    ( k4_xboole_0(esk10_0,esk11_0) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_110]),c_0_95]),c_0_83])])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_tarski(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_112]),c_0_113])).

cnf(c_0_115,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_114,c_0_48]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 1.46/1.65  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 1.46/1.65  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.46/1.65  #
% 1.46/1.65  # Preprocessing time       : 0.029 s
% 1.46/1.65  
% 1.46/1.65  # Proof found!
% 1.46/1.65  # SZS status Theorem
% 1.46/1.65  # SZS output start CNFRefutation
% 1.46/1.65  fof(t14_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X3,X2))&![X4]:((r1_tarski(X1,X4)&r1_tarski(X3,X4))=>r1_tarski(X2,X4)))=>X2=k2_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 1.46/1.65  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.46/1.65  fof(t31_relat_1, conjecture, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 1.46/1.65  fof(t43_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,k2_xboole_0(X2,X3))=>r1_tarski(k4_xboole_0(X1,X2),X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.46/1.65  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.46/1.65  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.46/1.65  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 1.46/1.65  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.46/1.65  fof(t8_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X3,X2))=>r1_tarski(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.46/1.65  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 1.46/1.65  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.46/1.65  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.46/1.65  fof(t44_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k4_xboole_0(X1,X2),X3)=>r1_tarski(X1,k2_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.46/1.65  fof(t10_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>r1_tarski(X1,k2_xboole_0(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.46/1.65  fof(t26_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 1.46/1.65  fof(t15_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_relat_1)).
% 1.46/1.65  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.46/1.65  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.46/1.65  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.46/1.65  fof(c_0_19, plain, ![X16, X17, X18]:(((r1_tarski(X16,esk3_3(X16,X17,X18))|(~r1_tarski(X16,X17)|~r1_tarski(X18,X17))|X17=k2_xboole_0(X16,X18))&(r1_tarski(X18,esk3_3(X16,X17,X18))|(~r1_tarski(X16,X17)|~r1_tarski(X18,X17))|X17=k2_xboole_0(X16,X18)))&(~r1_tarski(X17,esk3_3(X16,X17,X18))|(~r1_tarski(X16,X17)|~r1_tarski(X18,X17))|X17=k2_xboole_0(X16,X18))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t14_xboole_1])])])])).
% 1.46/1.65  fof(c_0_20, plain, ![X43, X44]:k3_tarski(k2_tarski(X43,X44))=k2_xboole_0(X43,X44), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.46/1.65  fof(c_0_21, negated_conjecture, ~(![X1]:(v1_relat_1(X1)=>![X2]:(v1_relat_1(X2)=>(r1_tarski(X1,X2)=>r1_tarski(k3_relat_1(X1),k3_relat_1(X2)))))), inference(assume_negation,[status(cth)],[t31_relat_1])).
% 1.46/1.65  fof(c_0_22, plain, ![X21, X22, X23]:(~r1_tarski(X21,k2_xboole_0(X22,X23))|r1_tarski(k4_xboole_0(X21,X22),X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_xboole_1])])).
% 1.46/1.65  fof(c_0_23, plain, ![X11, X12]:(((r1_tarski(X11,X12)|X11!=X12)&(r1_tarski(X12,X11)|X11!=X12))&(~r1_tarski(X11,X12)|~r1_tarski(X12,X11)|X11=X12)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 1.46/1.65  cnf(c_0_24, plain, (r1_tarski(X1,esk3_3(X2,X3,X1))|X3=k2_xboole_0(X2,X1)|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.46/1.65  cnf(c_0_25, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.46/1.65  fof(c_0_26, negated_conjecture, (v1_relat_1(esk10_0)&(v1_relat_1(esk11_0)&(r1_tarski(esk10_0,esk11_0)&~r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_21])])])).
% 1.46/1.65  fof(c_0_27, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 1.46/1.65  fof(c_0_28, plain, ![X32, X33, X34, X36, X37, X38, X39, X41]:((((r2_hidden(X34,esk4_3(X32,X33,X34))|~r2_hidden(X34,X33)|X33!=k3_tarski(X32))&(r2_hidden(esk4_3(X32,X33,X34),X32)|~r2_hidden(X34,X33)|X33!=k3_tarski(X32)))&(~r2_hidden(X36,X37)|~r2_hidden(X37,X32)|r2_hidden(X36,X33)|X33!=k3_tarski(X32)))&((~r2_hidden(esk5_2(X38,X39),X39)|(~r2_hidden(esk5_2(X38,X39),X41)|~r2_hidden(X41,X38))|X39=k3_tarski(X38))&((r2_hidden(esk5_2(X38,X39),esk6_2(X38,X39))|r2_hidden(esk5_2(X38,X39),X39)|X39=k3_tarski(X38))&(r2_hidden(esk6_2(X38,X39),X38)|r2_hidden(esk5_2(X38,X39),X39)|X39=k3_tarski(X38))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 1.46/1.65  cnf(c_0_29, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.46/1.65  cnf(c_0_30, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.46/1.65  cnf(c_0_31, plain, (X3=k3_tarski(k2_tarski(X2,X1))|r1_tarski(X1,esk3_3(X2,X3,X1))|~r1_tarski(X2,X3)|~r1_tarski(X1,X3)), inference(rw,[status(thm)],[c_0_24, c_0_25])).
% 1.46/1.65  cnf(c_0_32, negated_conjecture, (r1_tarski(esk10_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.46/1.65  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.46/1.65  cnf(c_0_34, plain, (r2_hidden(esk4_3(X1,X2,X3),X1)|~r2_hidden(X3,X2)|X2!=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 1.46/1.65  fof(c_0_35, plain, ![X9]:(X9=k1_xboole_0|r2_hidden(esk2_1(X9),X9)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 1.46/1.65  fof(c_0_36, plain, ![X29, X30, X31]:(~r1_tarski(X29,X30)|~r1_tarski(X31,X30)|r1_tarski(k2_xboole_0(X29,X31),X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_xboole_1])])).
% 1.46/1.65  cnf(c_0_37, plain, (r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))), inference(rw,[status(thm)],[c_0_29, c_0_25])).
% 1.46/1.65  cnf(c_0_38, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_30])).
% 1.46/1.65  cnf(c_0_39, negated_conjecture, (k3_tarski(k2_tarski(esk10_0,X1))=esk11_0|r1_tarski(X1,esk3_3(esk10_0,esk11_0,X1))|~r1_tarski(X1,esk11_0)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.46/1.65  fof(c_0_40, plain, ![X47, X48, X49, X51, X52, X53, X54, X56]:(((~r2_hidden(X49,X48)|r2_hidden(k4_tarski(X49,esk7_3(X47,X48,X49)),X47)|X48!=k1_relat_1(X47))&(~r2_hidden(k4_tarski(X51,X52),X47)|r2_hidden(X51,X48)|X48!=k1_relat_1(X47)))&((~r2_hidden(esk8_2(X53,X54),X54)|~r2_hidden(k4_tarski(esk8_2(X53,X54),X56),X53)|X54=k1_relat_1(X53))&(r2_hidden(esk8_2(X53,X54),X54)|r2_hidden(k4_tarski(esk8_2(X53,X54),esk9_2(X53,X54)),X53)|X54=k1_relat_1(X53)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.46/1.65  cnf(c_0_41, plain, (X1!=k3_tarski(X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 1.46/1.65  cnf(c_0_42, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 1.46/1.65  fof(c_0_43, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.46/1.65  fof(c_0_44, plain, ![X58]:(~v1_relat_1(X58)|k3_relat_1(X58)=k2_xboole_0(k1_relat_1(X58),k2_relat_1(X58))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.46/1.65  cnf(c_0_45, plain, (r1_tarski(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)|~r1_tarski(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 1.46/1.65  fof(c_0_46, plain, ![X24, X25, X26]:(~r1_tarski(k4_xboole_0(X24,X25),X26)|r1_tarski(X24,k2_xboole_0(X25,X26))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_xboole_1])])).
% 1.46/1.65  cnf(c_0_47, plain, (X1=k2_xboole_0(X2,X3)|~r1_tarski(X1,esk3_3(X2,X1,X3))|~r1_tarski(X2,X1)|~r1_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.46/1.65  cnf(c_0_48, plain, (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X1),X2)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 1.46/1.65  cnf(c_0_49, negated_conjecture, (k3_tarski(k2_tarski(esk10_0,esk11_0))=esk11_0|r1_tarski(esk11_0,esk3_3(esk10_0,esk11_0,esk11_0))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 1.46/1.65  cnf(c_0_50, plain, (r2_hidden(k4_tarski(X1,esk7_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.46/1.65  cnf(c_0_51, plain, (X1=k1_xboole_0|X1!=k3_tarski(X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.46/1.65  cnf(c_0_52, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 1.46/1.65  cnf(c_0_53, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 1.46/1.65  fof(c_0_54, plain, ![X13, X14, X15]:(~r1_tarski(X13,X14)|r1_tarski(X13,k2_xboole_0(X15,X14))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_xboole_1])])).
% 1.46/1.65  fof(c_0_55, plain, ![X61, X62]:(~v1_relat_1(X61)|(~v1_relat_1(X62)|k2_relat_1(k2_xboole_0(X61,X62))=k2_xboole_0(k2_relat_1(X61),k2_relat_1(X62)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t26_relat_1])])])).
% 1.46/1.65  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.46/1.65  cnf(c_0_57, plain, (r1_tarski(k3_tarski(k2_tarski(X1,X3)),X2)|~r1_tarski(X3,X2)|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_45, c_0_25])).
% 1.46/1.65  cnf(c_0_58, plain, (r1_tarski(X1,k2_xboole_0(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 1.46/1.65  cnf(c_0_59, plain, (X1=k3_tarski(k2_tarski(X2,X3))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)|~r1_tarski(X1,esk3_3(X2,X1,X3))), inference(rw,[status(thm)],[c_0_47, c_0_25])).
% 1.46/1.65  cnf(c_0_60, negated_conjecture, (r1_tarski(esk11_0,esk3_3(esk10_0,esk11_0,esk11_0))|r1_tarski(k4_xboole_0(esk11_0,esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.46/1.65  fof(c_0_61, plain, ![X59, X60]:(~v1_relat_1(X59)|(~v1_relat_1(X60)|r1_tarski(k6_subset_1(k1_relat_1(X59),k1_relat_1(X60)),k1_relat_1(k6_subset_1(X59,X60))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t15_relat_1])])])).
% 1.46/1.65  fof(c_0_62, plain, ![X45, X46]:k6_subset_1(X45,X46)=k4_xboole_0(X45,X46), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 1.46/1.65  cnf(c_0_63, plain, (X1!=k1_relat_1(X2)|~r2_hidden(X3,X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_50])).
% 1.46/1.65  cnf(c_0_64, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 1.46/1.65  cnf(c_0_65, plain, (k3_tarski(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_51])).
% 1.46/1.65  cnf(c_0_66, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 1.46/1.65  cnf(c_0_67, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X1,X2)))), inference(rw,[status(thm)],[c_0_52, c_0_25])).
% 1.46/1.65  cnf(c_0_68, plain, (k3_relat_1(X1)=k3_tarski(k2_tarski(k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_53, c_0_25])).
% 1.46/1.65  cnf(c_0_69, plain, (r1_tarski(X1,k2_xboole_0(X3,X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 1.46/1.65  cnf(c_0_70, plain, (k2_relat_1(k2_xboole_0(X1,X2))=k2_xboole_0(k2_relat_1(X1),k2_relat_1(X2))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 1.46/1.65  cnf(c_0_71, plain, (X1=k3_tarski(k2_tarski(X2,X3))|~r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 1.46/1.65  cnf(c_0_72, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X2,X3)))|~r1_tarski(k4_xboole_0(X1,X2),X3)), inference(rw,[status(thm)],[c_0_58, c_0_25])).
% 1.46/1.65  cnf(c_0_73, negated_conjecture, (k3_tarski(k2_tarski(esk10_0,esk11_0))=esk11_0|r1_tarski(k4_xboole_0(esk11_0,esk10_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_60]), c_0_38]), c_0_32])])).
% 1.46/1.65  cnf(c_0_74, plain, (r1_tarski(k6_subset_1(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k6_subset_1(X1,X2)))|~v1_relat_1(X1)|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 1.46/1.65  cnf(c_0_75, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 1.46/1.65  cnf(c_0_76, plain, (X1=k1_xboole_0|X1!=k1_relat_1(X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_63, c_0_42])).
% 1.46/1.65  cnf(c_0_77, plain, (v1_xboole_0(X1)|X1!=k3_tarski(X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_64])).
% 1.46/1.65  cnf(c_0_78, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 1.46/1.65  fof(c_0_79, plain, ![X20]:r1_tarski(k1_xboole_0,X20), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 1.46/1.65  cnf(c_0_80, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(k3_tarski(k2_tarski(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_56, c_0_67])).
% 1.46/1.65  cnf(c_0_81, negated_conjecture, (~r1_tarski(k3_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.46/1.65  cnf(c_0_82, plain, (r1_tarski(k3_relat_1(X1),X2)|~v1_relat_1(X1)|~r1_tarski(k2_relat_1(X1),X2)|~r1_tarski(k1_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_57, c_0_68])).
% 1.46/1.65  cnf(c_0_83, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.46/1.65  cnf(c_0_84, plain, (r1_tarski(X1,k3_tarski(k2_tarski(X3,X2)))|~r1_tarski(X1,X2)), inference(rw,[status(thm)],[c_0_69, c_0_25])).
% 1.46/1.65  cnf(c_0_85, plain, (k2_relat_1(k3_tarski(k2_tarski(X1,X2)))=k3_tarski(k2_tarski(k2_relat_1(X1),k2_relat_1(X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_70, c_0_25]), c_0_25])).
% 1.46/1.65  cnf(c_0_86, plain, (X1=k3_tarski(k2_tarski(X2,X3))|~r1_tarski(k4_xboole_0(X1,X2),X3)|~r1_tarski(X3,X1)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 1.46/1.65  cnf(c_0_87, negated_conjecture, (r1_tarski(k4_xboole_0(esk11_0,esk10_0),esk11_0)), inference(spm,[status(thm)],[c_0_48, c_0_73])).
% 1.46/1.65  cnf(c_0_88, plain, (r1_tarski(k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)),k1_relat_1(k4_xboole_0(X1,X2)))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75]), c_0_75])).
% 1.46/1.65  cnf(c_0_89, plain, (k1_relat_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(er,[status(thm)],[c_0_76])).
% 1.46/1.65  cnf(c_0_90, plain, (v1_xboole_0(X1)|X1!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_78]), c_0_66])])).
% 1.46/1.65  cnf(c_0_91, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_79])).
% 1.46/1.65  cnf(c_0_92, plain, (k3_tarski(k2_tarski(X1,X2))=X1|~r1_tarski(X2,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_57]), c_0_38])])).
% 1.46/1.65  cnf(c_0_93, negated_conjecture, (~r1_tarski(k2_relat_1(esk10_0),k3_relat_1(esk11_0))|~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_83])])).
% 1.46/1.65  cnf(c_0_94, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(X1,k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_84, c_0_68])).
% 1.46/1.65  cnf(c_0_95, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 1.46/1.65  cnf(c_0_96, plain, (r1_tarski(k2_relat_1(X1),k2_relat_1(k3_tarski(k2_tarski(X1,X2))))|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_67, c_0_85])).
% 1.46/1.65  cnf(c_0_97, negated_conjecture, (k3_tarski(k2_tarski(esk10_0,esk11_0))=esk11_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_87]), c_0_38]), c_0_32])])).
% 1.46/1.65  cnf(c_0_98, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_relat_1(k4_xboole_0(X1,X2))|~v1_relat_1(X2)|~v1_relat_1(X1)|~r1_tarski(k1_relat_1(k4_xboole_0(X1,X2)),k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2)))), inference(spm,[status(thm)],[c_0_56, c_0_88])).
% 1.46/1.65  cnf(c_0_99, plain, (k1_relat_1(X1)=k1_xboole_0|X1!=k1_xboole_0), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 1.46/1.65  cnf(c_0_100, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_56, c_0_91])).
% 1.46/1.65  cnf(c_0_101, plain, (r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3),X4)|~r1_tarski(X2,k3_tarski(k2_tarski(X3,X4)))|~r1_tarski(X1,k3_tarski(k2_tarski(X3,X4)))), inference(spm,[status(thm)],[c_0_37, c_0_57])).
% 1.46/1.65  cnf(c_0_102, plain, (r1_tarski(X1,X2)|~r1_tarski(X1,X3)|~r1_tarski(X3,X2)), inference(spm,[status(thm)],[c_0_84, c_0_92])).
% 1.46/1.65  cnf(c_0_103, negated_conjecture, (~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))|~r1_tarski(k2_relat_1(esk10_0),k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_95])])).
% 1.46/1.65  cnf(c_0_104, negated_conjecture, (r1_tarski(k2_relat_1(esk10_0),k2_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_96, c_0_97]), c_0_95]), c_0_83])])).
% 1.46/1.65  cnf(c_0_105, plain, (r1_tarski(X1,k3_relat_1(X2))|~v1_relat_1(X2)|~r1_tarski(k4_xboole_0(X1,k1_relat_1(X2)),k2_relat_1(X2))), inference(spm,[status(thm)],[c_0_72, c_0_68])).
% 1.46/1.65  cnf(c_0_106, plain, (k4_xboole_0(k1_relat_1(X1),k1_relat_1(X2))=k1_xboole_0|k4_xboole_0(X1,X2)!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_99]), c_0_91])])).
% 1.46/1.65  cnf(c_0_107, plain, (k4_xboole_0(k3_tarski(k2_tarski(X1,X2)),X3)=k1_xboole_0|~r1_tarski(X2,k3_tarski(k2_tarski(X3,k1_xboole_0)))|~r1_tarski(X1,k3_tarski(k2_tarski(X3,k1_xboole_0)))), inference(spm,[status(thm)],[c_0_100, c_0_101])).
% 1.46/1.65  cnf(c_0_108, negated_conjecture, (r1_tarski(esk10_0,X1)|~r1_tarski(esk11_0,X1)), inference(spm,[status(thm)],[c_0_102, c_0_32])).
% 1.46/1.65  cnf(c_0_109, negated_conjecture, (~r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103, c_0_104])])).
% 1.46/1.65  cnf(c_0_110, plain, (r1_tarski(k1_relat_1(X1),k3_relat_1(X2))|k4_xboole_0(X1,X2)!=k1_xboole_0|~v1_relat_1(X2)|~v1_relat_1(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_91])])).
% 1.46/1.65  cnf(c_0_111, plain, (k4_xboole_0(X1,X2)=k1_xboole_0|~r1_tarski(X1,k3_tarski(k2_tarski(X2,k1_xboole_0)))|~r1_tarski(X3,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_107, c_0_92]), c_0_102])).
% 1.46/1.65  cnf(c_0_112, negated_conjecture, (r1_tarski(esk10_0,k3_tarski(k2_tarski(esk11_0,X1)))), inference(spm,[status(thm)],[c_0_108, c_0_67])).
% 1.46/1.65  cnf(c_0_113, negated_conjecture, (k4_xboole_0(esk10_0,esk11_0)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_109, c_0_110]), c_0_95]), c_0_83])])).
% 1.46/1.65  cnf(c_0_114, negated_conjecture, (~r1_tarski(X1,esk10_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_111, c_0_112]), c_0_113])).
% 1.46/1.65  cnf(c_0_115, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_114, c_0_48]), ['proof']).
% 1.46/1.65  # SZS output end CNFRefutation
% 1.46/1.65  # Proof object total steps             : 116
% 1.46/1.65  # Proof object clause steps            : 78
% 1.46/1.65  # Proof object formula steps           : 38
% 1.46/1.65  # Proof object conjectures             : 22
% 1.46/1.65  # Proof object clause conjectures      : 19
% 1.46/1.65  # Proof object formula conjectures     : 3
% 1.46/1.65  # Proof object initial clauses used    : 25
% 1.46/1.65  # Proof object initial formulas used   : 19
% 1.46/1.65  # Proof object generating inferences   : 41
% 1.46/1.65  # Proof object simplifying inferences  : 41
% 1.46/1.65  # Training examples: 0 positive, 0 negative
% 1.46/1.65  # Parsed axioms                        : 19
% 1.46/1.65  # Removed by relevancy pruning/SinE    : 0
% 1.46/1.65  # Initial clauses                      : 35
% 1.46/1.65  # Removed in clause preprocessing      : 2
% 1.46/1.65  # Initial clauses in saturation        : 33
% 1.46/1.65  # Processed clauses                    : 5917
% 1.46/1.65  # ...of these trivial                  : 41
% 1.46/1.65  # ...subsumed                          : 3221
% 1.46/1.65  # ...remaining for further processing  : 2655
% 1.46/1.65  # Other redundant clauses eliminated   : 495
% 1.46/1.65  # Clauses deleted for lack of memory   : 0
% 1.46/1.65  # Backward-subsumed                    : 226
% 1.46/1.65  # Backward-rewritten                   : 15
% 1.46/1.65  # Generated clauses                    : 73471
% 1.46/1.65  # ...of the previous two non-trivial   : 68582
% 1.46/1.65  # Contextual simplify-reflections      : 70
% 1.46/1.65  # Paramodulations                      : 72714
% 1.46/1.65  # Factorizations                       : 26
% 1.46/1.65  # Equation resolutions                 : 724
% 1.46/1.65  # Propositional unsat checks           : 0
% 1.46/1.65  #    Propositional check models        : 0
% 1.46/1.65  #    Propositional check unsatisfiable : 0
% 1.46/1.65  #    Propositional clauses             : 0
% 1.46/1.65  #    Propositional clauses after purity: 0
% 1.46/1.65  #    Propositional unsat core size     : 0
% 1.46/1.65  #    Propositional preprocessing time  : 0.000
% 1.46/1.65  #    Propositional encoding time       : 0.000
% 1.46/1.65  #    Propositional solver time         : 0.000
% 1.46/1.65  #    Success case prop preproc time    : 0.000
% 1.46/1.65  #    Success case prop encoding time   : 0.000
% 1.46/1.65  #    Success case prop solver time     : 0.000
% 1.46/1.65  # Current number of processed clauses  : 2405
% 1.46/1.65  #    Positive orientable unit clauses  : 29
% 1.46/1.65  #    Positive unorientable unit clauses: 0
% 1.46/1.65  #    Negative unit clauses             : 17
% 1.46/1.65  #    Non-unit-clauses                  : 2359
% 1.46/1.65  # Current number of unprocessed clauses: 62284
% 1.46/1.65  # ...number of literals in the above   : 302797
% 1.46/1.65  # Current number of archived formulas  : 0
% 1.46/1.65  # Current number of archived clauses   : 250
% 1.46/1.65  # Clause-clause subsumption calls (NU) : 887524
% 1.46/1.65  # Rec. Clause-clause subsumption calls : 233366
% 1.46/1.65  # Non-unit clause-clause subsumptions  : 2926
% 1.46/1.65  # Unit Clause-clause subsumption calls : 8262
% 1.46/1.65  # Rewrite failures with RHS unbound    : 0
% 1.46/1.65  # BW rewrite match attempts            : 137
% 1.46/1.65  # BW rewrite match successes           : 9
% 1.46/1.65  # Condensation attempts                : 0
% 1.46/1.65  # Condensation successes               : 0
% 1.46/1.65  # Termbank termtop insertions          : 1398499
% 1.46/1.66  
% 1.46/1.66  # -------------------------------------------------
% 1.46/1.66  # User time                : 1.274 s
% 1.46/1.66  # System time              : 0.045 s
% 1.46/1.66  # Total time               : 1.318 s
% 1.46/1.66  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
