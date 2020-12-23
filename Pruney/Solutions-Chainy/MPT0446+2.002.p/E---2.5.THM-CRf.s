%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:20 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 208 expanded)
%              Number of clauses        :   41 (  85 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 330 expanded)
%              Number of equality atoms :   46 ( 153 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(fc1_subset_1,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t99_zfmisc_1,axiom,(
    ! [X1] : k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(t30_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(c_0_19,plain,(
    ! [X47,X48] : k3_tarski(k2_tarski(X47,X48)) = k2_xboole_0(X47,X48) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_20,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_21,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_22,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_24,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_25,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_26,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_27,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k5_enumset1(X32,X32,X33,X34,X35,X36,X37) = k4_enumset1(X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_28,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44) = k5_enumset1(X38,X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_29,plain,(
    ! [X53,X54] :
      ( ( ~ m1_subset_1(X53,k1_zfmisc_1(X54))
        | r1_tarski(X53,X54) )
      & ( ~ r1_tarski(X53,X54)
        | m1_subset_1(X53,k1_zfmisc_1(X54)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_32,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_35,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_36,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X51,X52] :
      ( ~ m1_subset_1(X51,X52)
      | v1_xboole_0(X52)
      | r2_hidden(X51,X52) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

fof(c_0_40,plain,(
    ! [X50] : ~ v1_xboole_0(k1_zfmisc_1(X50)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).

fof(c_0_41,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_tarski(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_42,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_44,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_46,plain,(
    ! [X45,X46] :
      ( ~ r2_hidden(X45,X46)
      | r1_tarski(X45,k3_tarski(X46)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_48,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45,c_0_23]),c_0_23]),c_0_32]),c_0_32]),c_0_33]),c_0_33]),c_0_34]),c_0_34]),c_0_35]),c_0_35]),c_0_36]),c_0_36])).

fof(c_0_49,plain,(
    ! [X49] : k3_tarski(k1_zfmisc_1(X49)) = X49 ),
    inference(variable_rename,[status(thm)],[t99_zfmisc_1])).

fof(c_0_50,plain,(
    ! [X66,X67,X68,X70,X71,X72,X73,X75] :
      ( ( ~ r2_hidden(X68,X67)
        | r2_hidden(k4_tarski(esk5_3(X66,X67,X68),X68),X66)
        | X67 != k2_relat_1(X66) )
      & ( ~ r2_hidden(k4_tarski(X71,X70),X66)
        | r2_hidden(X70,X67)
        | X67 != k2_relat_1(X66) )
      & ( ~ r2_hidden(esk6_2(X72,X73),X73)
        | ~ r2_hidden(k4_tarski(X75,esk6_2(X72,X73)),X72)
        | X73 = k2_relat_1(X72) )
      & ( r2_hidden(esk6_2(X72,X73),X73)
        | r2_hidden(k4_tarski(esk7_2(X72,X73),esk6_2(X72,X73)),X72)
        | X73 = k2_relat_1(X72) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_51,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
         => ( r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_relat_1])).

fof(c_0_52,plain,(
    ! [X77] :
      ( ~ v1_relat_1(X77)
      | k3_relat_1(X77) = k2_xboole_0(k1_relat_1(X77),k2_relat_1(X77)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_53,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_56,plain,
    ( k3_tarski(k1_zfmisc_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

fof(c_0_58,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)
    & ( ~ r2_hidden(esk8_0,k3_relat_1(esk10_0))
      | ~ r2_hidden(esk9_0,k3_relat_1(esk10_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).

cnf(c_0_59,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_62,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_57])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_64,plain,
    ( k3_relat_1(X1) = k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_35]),c_0_36])).

cnf(c_0_65,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

fof(c_0_66,plain,(
    ! [X55,X56,X57,X59,X60,X61,X62,X64] :
      ( ( ~ r2_hidden(X57,X56)
        | r2_hidden(k4_tarski(X57,esk2_3(X55,X56,X57)),X55)
        | X56 != k1_relat_1(X55) )
      & ( ~ r2_hidden(k4_tarski(X59,X60),X55)
        | r2_hidden(X59,X56)
        | X56 != k1_relat_1(X55) )
      & ( ~ r2_hidden(esk3_2(X61,X62),X62)
        | ~ r2_hidden(k4_tarski(esk3_2(X61,X62),X64),X61)
        | X62 = k1_relat_1(X61) )
      & ( r2_hidden(esk3_2(X61,X62),X62)
        | r2_hidden(k4_tarski(esk3_2(X61,X62),esk4_2(X61,X62)),X61)
        | X62 = k1_relat_1(X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk9_0,k2_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_69,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k2_relat_1(esk10_0))) = k3_relat_1(esk10_0) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_70,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk9_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_relat_1(esk10_0)))) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_69])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k3_relat_1(esk10_0))
    | ~ r2_hidden(esk9_0,k3_relat_1(esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_69])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk10_0))
    | ~ r2_hidden(X1,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_72])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk8_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k3_relat_1(esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74,c_0_75])])).

cnf(c_0_79,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:54:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.87/1.06  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.87/1.06  # and selection function SelectNegativeLiterals.
% 0.87/1.06  #
% 0.87/1.06  # Preprocessing time       : 0.028 s
% 0.87/1.06  # Presaturation interreduction done
% 0.87/1.06  
% 0.87/1.06  # Proof found!
% 0.87/1.06  # SZS status Theorem
% 0.87/1.06  # SZS output start CNFRefutation
% 0.87/1.06  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 0.87/1.06  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.87/1.06  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.87/1.06  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.87/1.06  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.87/1.06  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.87/1.06  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.87/1.06  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.87/1.06  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.87/1.06  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.87/1.06  fof(fc1_subset_1, axiom, ![X1]:~(v1_xboole_0(k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 0.87/1.06  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 0.87/1.06  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.87/1.06  fof(t99_zfmisc_1, axiom, ![X1]:k3_tarski(k1_zfmisc_1(X1))=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 0.87/1.06  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.87/1.06  fof(t30_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 0.87/1.06  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.87/1.06  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.87/1.06  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.87/1.06  fof(c_0_19, plain, ![X47, X48]:k3_tarski(k2_tarski(X47,X48))=k2_xboole_0(X47,X48), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 0.87/1.06  fof(c_0_20, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.87/1.06  fof(c_0_21, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.87/1.06  cnf(c_0_22, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.87/1.06  cnf(c_0_23, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.87/1.06  fof(c_0_24, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.87/1.06  fof(c_0_25, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.87/1.06  fof(c_0_26, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.87/1.06  fof(c_0_27, plain, ![X32, X33, X34, X35, X36, X37]:k5_enumset1(X32,X32,X33,X34,X35,X36,X37)=k4_enumset1(X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.87/1.06  fof(c_0_28, plain, ![X38, X39, X40, X41, X42, X43, X44]:k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44)=k5_enumset1(X38,X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.87/1.06  fof(c_0_29, plain, ![X53, X54]:((~m1_subset_1(X53,k1_zfmisc_1(X54))|r1_tarski(X53,X54))&(~r1_tarski(X53,X54)|m1_subset_1(X53,k1_zfmisc_1(X54)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.87/1.06  cnf(c_0_30, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.87/1.06  cnf(c_0_31, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.87/1.06  cnf(c_0_32, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.87/1.06  cnf(c_0_33, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.87/1.06  cnf(c_0_34, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.87/1.06  cnf(c_0_35, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.87/1.06  cnf(c_0_36, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.87/1.06  fof(c_0_37, plain, ![X51, X52]:(~m1_subset_1(X51,X52)|(v1_xboole_0(X52)|r2_hidden(X51,X52))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.87/1.06  cnf(c_0_38, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.87/1.06  cnf(c_0_39, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.87/1.06  fof(c_0_40, plain, ![X50]:~v1_xboole_0(k1_zfmisc_1(X50)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc1_subset_1])])).
% 0.87/1.06  fof(c_0_41, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_tarski(X17,X16), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 0.87/1.06  cnf(c_0_42, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.87/1.06  cnf(c_0_43, plain, (m1_subset_1(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.87/1.06  cnf(c_0_44, plain, (~v1_xboole_0(k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.87/1.06  cnf(c_0_45, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.87/1.06  fof(c_0_46, plain, ![X45, X46]:(~r2_hidden(X45,X46)|r1_tarski(X45,k3_tarski(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.87/1.06  cnf(c_0_47, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.87/1.06  cnf(c_0_48, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_45, c_0_23]), c_0_23]), c_0_32]), c_0_32]), c_0_33]), c_0_33]), c_0_34]), c_0_34]), c_0_35]), c_0_35]), c_0_36]), c_0_36])).
% 0.87/1.06  fof(c_0_49, plain, ![X49]:k3_tarski(k1_zfmisc_1(X49))=X49, inference(variable_rename,[status(thm)],[t99_zfmisc_1])).
% 0.87/1.06  fof(c_0_50, plain, ![X66, X67, X68, X70, X71, X72, X73, X75]:(((~r2_hidden(X68,X67)|r2_hidden(k4_tarski(esk5_3(X66,X67,X68),X68),X66)|X67!=k2_relat_1(X66))&(~r2_hidden(k4_tarski(X71,X70),X66)|r2_hidden(X70,X67)|X67!=k2_relat_1(X66)))&((~r2_hidden(esk6_2(X72,X73),X73)|~r2_hidden(k4_tarski(X75,esk6_2(X72,X73)),X72)|X73=k2_relat_1(X72))&(r2_hidden(esk6_2(X72,X73),X73)|r2_hidden(k4_tarski(esk7_2(X72,X73),esk6_2(X72,X73)),X72)|X73=k2_relat_1(X72)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.87/1.06  fof(c_0_51, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3)))))), inference(assume_negation,[status(cth)],[t30_relat_1])).
% 0.87/1.06  fof(c_0_52, plain, ![X77]:(~v1_relat_1(X77)|k3_relat_1(X77)=k2_xboole_0(k1_relat_1(X77),k2_relat_1(X77))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.87/1.06  fof(c_0_53, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.87/1.06  cnf(c_0_54, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.87/1.06  cnf(c_0_55, plain, (r2_hidden(X1,k1_zfmisc_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.87/1.06  cnf(c_0_56, plain, (k3_tarski(k1_zfmisc_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.87/1.06  cnf(c_0_57, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.87/1.06  fof(c_0_58, negated_conjecture, (v1_relat_1(esk10_0)&(r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)&(~r2_hidden(esk8_0,k3_relat_1(esk10_0))|~r2_hidden(esk9_0,k3_relat_1(esk10_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_51])])])).
% 0.87/1.06  cnf(c_0_59, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.87/1.06  cnf(c_0_60, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.87/1.06  cnf(c_0_61, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.87/1.06  cnf(c_0_62, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_57])).
% 0.87/1.06  cnf(c_0_63, negated_conjecture, (r2_hidden(k4_tarski(esk8_0,esk9_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.87/1.06  cnf(c_0_64, plain, (k3_relat_1(X1)=k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_35]), c_0_36])).
% 0.87/1.06  cnf(c_0_65, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.87/1.06  fof(c_0_66, plain, ![X55, X56, X57, X59, X60, X61, X62, X64]:(((~r2_hidden(X57,X56)|r2_hidden(k4_tarski(X57,esk2_3(X55,X56,X57)),X55)|X56!=k1_relat_1(X55))&(~r2_hidden(k4_tarski(X59,X60),X55)|r2_hidden(X59,X56)|X56!=k1_relat_1(X55)))&((~r2_hidden(esk3_2(X61,X62),X62)|~r2_hidden(k4_tarski(esk3_2(X61,X62),X64),X61)|X62=k1_relat_1(X61))&(r2_hidden(esk3_2(X61,X62),X62)|r2_hidden(k4_tarski(esk3_2(X61,X62),esk4_2(X61,X62)),X61)|X62=k1_relat_1(X61)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.87/1.06  cnf(c_0_67, plain, (r2_hidden(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.87/1.06  cnf(c_0_68, negated_conjecture, (r2_hidden(esk9_0,k2_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.87/1.06  cnf(c_0_69, negated_conjecture, (k3_tarski(k6_enumset1(k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k1_relat_1(esk10_0),k2_relat_1(esk10_0)))=k3_relat_1(esk10_0)), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.87/1.06  cnf(c_0_70, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.87/1.06  cnf(c_0_71, negated_conjecture, (r2_hidden(esk9_0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k2_relat_1(esk10_0))))), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.87/1.06  cnf(c_0_72, negated_conjecture, (r1_tarski(k1_relat_1(esk10_0),k3_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_39, c_0_69])).
% 0.87/1.06  cnf(c_0_73, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_70])).
% 0.87/1.06  cnf(c_0_74, negated_conjecture, (~r2_hidden(esk8_0,k3_relat_1(esk10_0))|~r2_hidden(esk9_0,k3_relat_1(esk10_0))), inference(split_conjunct,[status(thm)],[c_0_58])).
% 0.87/1.06  cnf(c_0_75, negated_conjecture, (r2_hidden(esk9_0,k3_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_71, c_0_69])).
% 0.87/1.06  cnf(c_0_76, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk10_0))|~r2_hidden(X1,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_60, c_0_72])).
% 0.87/1.06  cnf(c_0_77, negated_conjecture, (r2_hidden(esk8_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_73, c_0_63])).
% 0.87/1.06  cnf(c_0_78, negated_conjecture, (~r2_hidden(esk8_0,k3_relat_1(esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_74, c_0_75])])).
% 0.87/1.06  cnf(c_0_79, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_77]), c_0_78]), ['proof']).
% 0.87/1.06  # SZS output end CNFRefutation
% 0.87/1.06  # Proof object total steps             : 80
% 0.87/1.06  # Proof object clause steps            : 41
% 0.87/1.06  # Proof object formula steps           : 39
% 0.87/1.06  # Proof object conjectures             : 15
% 0.87/1.06  # Proof object clause conjectures      : 12
% 0.87/1.06  # Proof object formula conjectures     : 3
% 0.87/1.06  # Proof object initial clauses used    : 21
% 0.87/1.06  # Proof object initial formulas used   : 19
% 0.87/1.06  # Proof object generating inferences   : 13
% 0.87/1.06  # Proof object simplifying inferences  : 32
% 0.87/1.06  # Training examples: 0 positive, 0 negative
% 0.87/1.06  # Parsed axioms                        : 19
% 0.87/1.06  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.06  # Initial clauses                      : 30
% 0.87/1.06  # Removed in clause preprocessing      : 7
% 0.87/1.06  # Initial clauses in saturation        : 23
% 0.87/1.06  # Processed clauses                    : 983
% 0.87/1.06  # ...of these trivial                  : 5
% 0.87/1.06  # ...subsumed                          : 174
% 0.87/1.06  # ...remaining for further processing  : 804
% 0.87/1.06  # Other redundant clauses eliminated   : 4
% 0.87/1.06  # Clauses deleted for lack of memory   : 0
% 0.87/1.06  # Backward-subsumed                    : 8
% 0.87/1.06  # Backward-rewritten                   : 6
% 0.87/1.06  # Generated clauses                    : 59776
% 0.87/1.06  # ...of the previous two non-trivial   : 59473
% 0.87/1.06  # Contextual simplify-reflections      : 2
% 0.87/1.06  # Paramodulations                      : 59764
% 0.87/1.06  # Factorizations                       : 8
% 0.87/1.06  # Equation resolutions                 : 4
% 0.87/1.06  # Propositional unsat checks           : 0
% 0.87/1.06  #    Propositional check models        : 0
% 0.87/1.06  #    Propositional check unsatisfiable : 0
% 0.87/1.06  #    Propositional clauses             : 0
% 0.87/1.06  #    Propositional clauses after purity: 0
% 0.87/1.06  #    Propositional unsat core size     : 0
% 0.87/1.06  #    Propositional preprocessing time  : 0.000
% 0.87/1.06  #    Propositional encoding time       : 0.000
% 0.87/1.06  #    Propositional solver time         : 0.000
% 0.87/1.06  #    Success case prop preproc time    : 0.000
% 0.87/1.06  #    Success case prop encoding time   : 0.000
% 0.87/1.06  #    Success case prop solver time     : 0.000
% 0.87/1.06  # Current number of processed clauses  : 763
% 0.87/1.06  #    Positive orientable unit clauses  : 308
% 0.87/1.06  #    Positive unorientable unit clauses: 1
% 0.87/1.06  #    Negative unit clauses             : 2
% 0.87/1.06  #    Non-unit-clauses                  : 452
% 0.87/1.06  # Current number of unprocessed clauses: 58501
% 0.87/1.06  # ...number of literals in the above   : 239340
% 0.87/1.06  # Current number of archived formulas  : 0
% 0.87/1.06  # Current number of archived clauses   : 44
% 0.87/1.06  # Clause-clause subsumption calls (NU) : 25051
% 0.87/1.06  # Rec. Clause-clause subsumption calls : 18708
% 0.87/1.06  # Non-unit clause-clause subsumptions  : 184
% 0.87/1.06  # Unit Clause-clause subsumption calls : 1535
% 0.87/1.06  # Rewrite failures with RHS unbound    : 0
% 0.87/1.06  # BW rewrite match attempts            : 2144
% 0.87/1.06  # BW rewrite match successes           : 7
% 0.87/1.06  # Condensation attempts                : 0
% 0.87/1.06  # Condensation successes               : 0
% 0.87/1.06  # Termbank termtop insertions          : 1619478
% 0.87/1.06  
% 0.87/1.06  # -------------------------------------------------
% 0.87/1.06  # User time                : 0.666 s
% 0.87/1.06  # System time              : 0.056 s
% 0.87/1.06  # Total time               : 0.722 s
% 0.87/1.06  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
