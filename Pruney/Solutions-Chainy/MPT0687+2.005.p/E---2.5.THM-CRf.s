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
% DateTime   : Thu Dec  3 10:54:35 EST 2020

% Result     : Theorem 0.53s
% Output     : CNFRefutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 269 expanded)
%              Number of clauses        :   49 ( 115 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  243 ( 582 expanded)
%              Number of equality atoms :  119 ( 304 expanded)
%              Maximal formula depth    :   32 (   4 average)
%              Maximal clause size      :   44 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t173_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t142_funct_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(d3_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( X6 = k3_enumset1(X1,X2,X3,X4,X5)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X7 != X1
              & X7 != X2
              & X7 != X3
              & X7 != X4
              & X7 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ~ r1_xboole_0(X8,X9)
      | r1_xboole_0(X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_19,plain,(
    ! [X10,X11] : r1_xboole_0(k4_xboole_0(X10,X11),X11) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_20,plain,(
    ! [X44,X45] :
      ( ( k2_zfmisc_1(X44,X45) != k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 )
      & ( X45 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_21,plain,(
    ! [X86,X87] :
      ( ( k10_relat_1(X87,X86) != k1_xboole_0
        | r1_xboole_0(k2_relat_1(X87),X86)
        | ~ v1_relat_1(X87) )
      & ( ~ r1_xboole_0(k2_relat_1(X87),X86)
        | k10_relat_1(X87,X86) = k1_xboole_0
        | ~ v1_relat_1(X87) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).

cnf(c_0_22,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
        <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t142_funct_1])).

fof(c_0_25,plain,(
    ! [X42,X43] :
      ( r2_hidden(X42,X43)
      | r1_xboole_0(k1_tarski(X42),X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

fof(c_0_26,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_27,plain,(
    ! [X15,X16] : k1_enumset1(X15,X15,X16) = k2_tarski(X15,X16) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_28,plain,(
    ! [X17,X18,X19] : k2_enumset1(X17,X17,X18,X19) = k1_enumset1(X17,X18,X19) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_29,plain,(
    ! [X20,X21,X22,X23] : k3_enumset1(X20,X20,X21,X22,X23) = k2_enumset1(X20,X21,X22,X23) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_30,plain,(
    ! [X24,X25,X26,X27,X28] : k4_enumset1(X24,X24,X25,X26,X27,X28) = k3_enumset1(X24,X25,X26,X27,X28) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_31,plain,(
    ! [X29,X30,X31,X32,X33,X34] : k5_enumset1(X29,X29,X30,X31,X32,X33,X34) = k4_enumset1(X29,X30,X31,X32,X33,X34) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_32,plain,(
    ! [X35,X36,X37,X38,X39,X40,X41] : k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41) = k5_enumset1(X35,X36,X37,X38,X39,X40,X41) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_33,plain,(
    ! [X46,X47] : ~ r2_hidden(X46,k2_zfmisc_1(X46,X47)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_34,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_36,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_37,negated_conjecture,
    ( v1_relat_1(esk9_0)
    & ( ~ r2_hidden(esk8_0,k2_relat_1(esk9_0))
      | k10_relat_1(esk9_0,k1_tarski(esk8_0)) = k1_xboole_0 )
    & ( r2_hidden(esk8_0,k2_relat_1(esk9_0))
      | k10_relat_1(esk9_0,k1_tarski(esk8_0)) != k1_xboole_0 ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_38,plain,(
    ! [X12,X13] :
      ( ( ~ r1_xboole_0(X12,X13)
        | k4_xboole_0(X12,X13) = X12 )
      & ( k4_xboole_0(X12,X13) != X12
        | r1_xboole_0(X12,X13) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_41,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_42,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_44,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_48,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_34])).

fof(c_0_49,plain,(
    ! [X75,X76,X77,X79,X80,X81,X82,X84] :
      ( ( ~ r2_hidden(X77,X76)
        | r2_hidden(k4_tarski(esk5_3(X75,X76,X77),X77),X75)
        | X76 != k2_relat_1(X75) )
      & ( ~ r2_hidden(k4_tarski(X80,X79),X75)
        | r2_hidden(X79,X76)
        | X76 != k2_relat_1(X75) )
      & ( ~ r2_hidden(esk6_2(X81,X82),X82)
        | ~ r2_hidden(k4_tarski(X84,esk6_2(X81,X82)),X81)
        | X82 = k2_relat_1(X81) )
      & ( r2_hidden(esk6_2(X81,X82),X82)
        | r2_hidden(k4_tarski(esk7_2(X81,X82),esk6_2(X81,X82)),X81)
        | X82 = k2_relat_1(X81) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_50,plain,
    ( k10_relat_1(X1,k4_xboole_0(X2,k2_relat_1(X1))) = k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( v1_relat_1(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_54,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk9_0))
    | k10_relat_1(esk9_0,k1_tarski(esk8_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_57,negated_conjecture,
    ( k10_relat_1(esk9_0,k4_xboole_0(X1,k2_relat_1(esk9_0))) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,plain,
    ( k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_59,plain,
    ( X1 = k2_relat_1(k1_xboole_0)
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_60,negated_conjecture,
    ( k10_relat_1(esk9_0,k1_tarski(esk8_0)) = k1_xboole_0
    | ~ r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk9_0))
    | k10_relat_1(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_62,negated_conjecture,
    ( k10_relat_1(esk9_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

fof(c_0_63,plain,(
    ! [X63,X64,X65,X66,X68,X69,X70,X71,X73] :
      ( ( r2_hidden(k4_tarski(X66,esk2_4(X63,X64,X65,X66)),X63)
        | ~ r2_hidden(X66,X65)
        | X65 != k10_relat_1(X63,X64)
        | ~ v1_relat_1(X63) )
      & ( r2_hidden(esk2_4(X63,X64,X65,X66),X64)
        | ~ r2_hidden(X66,X65)
        | X65 != k10_relat_1(X63,X64)
        | ~ v1_relat_1(X63) )
      & ( ~ r2_hidden(k4_tarski(X68,X69),X63)
        | ~ r2_hidden(X69,X64)
        | r2_hidden(X68,X65)
        | X65 != k10_relat_1(X63,X64)
        | ~ v1_relat_1(X63) )
      & ( ~ r2_hidden(esk3_3(X63,X70,X71),X71)
        | ~ r2_hidden(k4_tarski(esk3_3(X63,X70,X71),X73),X63)
        | ~ r2_hidden(X73,X70)
        | X71 = k10_relat_1(X63,X70)
        | ~ v1_relat_1(X63) )
      & ( r2_hidden(k4_tarski(esk3_3(X63,X70,X71),esk4_3(X63,X70,X71)),X63)
        | r2_hidden(esk3_3(X63,X70,X71),X71)
        | X71 = k10_relat_1(X63,X70)
        | ~ v1_relat_1(X63) )
      & ( r2_hidden(esk4_3(X63,X70,X71),X70)
        | r2_hidden(esk3_3(X63,X70,X71),X71)
        | X71 = k10_relat_1(X63,X70)
        | ~ v1_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_64,plain,
    ( r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_54,c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( k10_relat_1(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) = k1_xboole_0
    | ~ r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60,c_0_40]),c_0_41]),c_0_42]),c_0_43]),c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(esk8_0,k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

fof(c_0_68,plain,(
    ! [X48,X49,X50,X51,X52,X53,X54,X55,X56,X57,X58,X59,X60,X61] :
      ( ( ~ r2_hidden(X54,X53)
        | X54 = X48
        | X54 = X49
        | X54 = X50
        | X54 = X51
        | X54 = X52
        | X53 != k3_enumset1(X48,X49,X50,X51,X52) )
      & ( X55 != X48
        | r2_hidden(X55,X53)
        | X53 != k3_enumset1(X48,X49,X50,X51,X52) )
      & ( X55 != X49
        | r2_hidden(X55,X53)
        | X53 != k3_enumset1(X48,X49,X50,X51,X52) )
      & ( X55 != X50
        | r2_hidden(X55,X53)
        | X53 != k3_enumset1(X48,X49,X50,X51,X52) )
      & ( X55 != X51
        | r2_hidden(X55,X53)
        | X53 != k3_enumset1(X48,X49,X50,X51,X52) )
      & ( X55 != X52
        | r2_hidden(X55,X53)
        | X53 != k3_enumset1(X48,X49,X50,X51,X52) )
      & ( esk1_6(X56,X57,X58,X59,X60,X61) != X56
        | ~ r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)
        | X61 = k3_enumset1(X56,X57,X58,X59,X60) )
      & ( esk1_6(X56,X57,X58,X59,X60,X61) != X57
        | ~ r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)
        | X61 = k3_enumset1(X56,X57,X58,X59,X60) )
      & ( esk1_6(X56,X57,X58,X59,X60,X61) != X58
        | ~ r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)
        | X61 = k3_enumset1(X56,X57,X58,X59,X60) )
      & ( esk1_6(X56,X57,X58,X59,X60,X61) != X59
        | ~ r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)
        | X61 = k3_enumset1(X56,X57,X58,X59,X60) )
      & ( esk1_6(X56,X57,X58,X59,X60,X61) != X60
        | ~ r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)
        | X61 = k3_enumset1(X56,X57,X58,X59,X60) )
      & ( r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)
        | esk1_6(X56,X57,X58,X59,X60,X61) = X56
        | esk1_6(X56,X57,X58,X59,X60,X61) = X57
        | esk1_6(X56,X57,X58,X59,X60,X61) = X58
        | esk1_6(X56,X57,X58,X59,X60,X61) = X59
        | esk1_6(X56,X57,X58,X59,X60,X61) = X60
        | X61 = k3_enumset1(X56,X57,X58,X59,X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,plain,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_54])).

cnf(c_0_71,plain,
    ( r1_xboole_0(k2_relat_1(X1),X2)
    | k10_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_72,negated_conjecture,
    ( k10_relat_1(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_73,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k3_enumset1(X4,X5,X6,X7,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( X1 != k1_xboole_0
    | ~ r2_hidden(X2,k4_xboole_0(X3,k2_relat_1(esk9_0)))
    | ~ r2_hidden(k4_tarski(X4,X2),esk9_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_57]),c_0_51])]),c_0_70])).

cnf(c_0_75,plain,
    ( r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_64])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(k2_relat_1(esk9_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_51])])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X2) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_44]),c_0_45]),c_0_46])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_relat_1(esk9_0)))
    | ~ r2_hidden(k4_tarski(X3,X1),esk9_0) ),
    inference(er,[status(thm)],[c_0_74])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_3(esk9_0,k2_relat_1(esk9_0),esk8_0),esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_75,c_0_67])).

cnf(c_0_80,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_relat_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_76])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | X2 != k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_82,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k4_xboole_0(X1,k2_relat_1(esk9_0))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_83,negated_conjecture,
    ( k4_xboole_0(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_relat_1(esk9_0)) = k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_80])).

cnf(c_0_84,plain,
    ( r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X1)) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_84])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.53/0.71  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_AE_CS_SP_PI_S0a
% 0.53/0.71  # and selection function SelectNegativeLiterals.
% 0.53/0.71  #
% 0.53/0.71  # Preprocessing time       : 0.029 s
% 0.53/0.71  
% 0.53/0.71  # Proof found!
% 0.53/0.71  # SZS status Theorem
% 0.53/0.71  # SZS output start CNFRefutation
% 0.53/0.71  fof(symmetry_r1_xboole_0, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)=>r1_xboole_0(X2,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 0.53/0.71  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.53/0.71  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.53/0.71  fof(t173_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.53/0.71  fof(t142_funct_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 0.53/0.71  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.53/0.71  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.53/0.71  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.53/0.71  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.53/0.71  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 0.53/0.71  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 0.53/0.71  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 0.53/0.71  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_enumset1)).
% 0.53/0.71  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.53/0.71  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.53/0.71  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 0.53/0.71  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.53/0.71  fof(d3_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:(X6=k3_enumset1(X1,X2,X3,X4,X5)<=>![X7]:(r2_hidden(X7,X6)<=>~(((((X7!=X1&X7!=X2)&X7!=X3)&X7!=X4)&X7!=X5)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 0.53/0.71  fof(c_0_18, plain, ![X8, X9]:(~r1_xboole_0(X8,X9)|r1_xboole_0(X9,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).
% 0.53/0.71  fof(c_0_19, plain, ![X10, X11]:r1_xboole_0(k4_xboole_0(X10,X11),X11), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.53/0.71  fof(c_0_20, plain, ![X44, X45]:((k2_zfmisc_1(X44,X45)!=k1_xboole_0|(X44=k1_xboole_0|X45=k1_xboole_0))&((X44!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0)&(X45!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.53/0.71  fof(c_0_21, plain, ![X86, X87]:((k10_relat_1(X87,X86)!=k1_xboole_0|r1_xboole_0(k2_relat_1(X87),X86)|~v1_relat_1(X87))&(~r1_xboole_0(k2_relat_1(X87),X86)|k10_relat_1(X87,X86)=k1_xboole_0|~v1_relat_1(X87))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t173_relat_1])])])).
% 0.53/0.71  cnf(c_0_22, plain, (r1_xboole_0(X2,X1)|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.53/0.71  cnf(c_0_23, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.53/0.71  fof(c_0_24, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0))), inference(assume_negation,[status(cth)],[t142_funct_1])).
% 0.53/0.71  fof(c_0_25, plain, ![X42, X43]:(r2_hidden(X42,X43)|r1_xboole_0(k1_tarski(X42),X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.53/0.71  fof(c_0_26, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.53/0.71  fof(c_0_27, plain, ![X15, X16]:k1_enumset1(X15,X15,X16)=k2_tarski(X15,X16), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.53/0.71  fof(c_0_28, plain, ![X17, X18, X19]:k2_enumset1(X17,X17,X18,X19)=k1_enumset1(X17,X18,X19), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.53/0.71  fof(c_0_29, plain, ![X20, X21, X22, X23]:k3_enumset1(X20,X20,X21,X22,X23)=k2_enumset1(X20,X21,X22,X23), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 0.53/0.71  fof(c_0_30, plain, ![X24, X25, X26, X27, X28]:k4_enumset1(X24,X24,X25,X26,X27,X28)=k3_enumset1(X24,X25,X26,X27,X28), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 0.53/0.71  fof(c_0_31, plain, ![X29, X30, X31, X32, X33, X34]:k5_enumset1(X29,X29,X30,X31,X32,X33,X34)=k4_enumset1(X29,X30,X31,X32,X33,X34), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 0.53/0.71  fof(c_0_32, plain, ![X35, X36, X37, X38, X39, X40, X41]:k6_enumset1(X35,X35,X36,X37,X38,X39,X40,X41)=k5_enumset1(X35,X36,X37,X38,X39,X40,X41), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 0.53/0.71  fof(c_0_33, plain, ![X46, X47]:~r2_hidden(X46,k2_zfmisc_1(X46,X47)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.53/0.71  cnf(c_0_34, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.53/0.71  cnf(c_0_35, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k2_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.71  cnf(c_0_36, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.53/0.71  fof(c_0_37, negated_conjecture, (v1_relat_1(esk9_0)&((~r2_hidden(esk8_0,k2_relat_1(esk9_0))|k10_relat_1(esk9_0,k1_tarski(esk8_0))=k1_xboole_0)&(r2_hidden(esk8_0,k2_relat_1(esk9_0))|k10_relat_1(esk9_0,k1_tarski(esk8_0))!=k1_xboole_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 0.53/0.71  fof(c_0_38, plain, ![X12, X13]:((~r1_xboole_0(X12,X13)|k4_xboole_0(X12,X13)=X12)&(k4_xboole_0(X12,X13)!=X12|r1_xboole_0(X12,X13))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.53/0.71  cnf(c_0_39, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.53/0.71  cnf(c_0_40, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.53/0.71  cnf(c_0_41, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.53/0.71  cnf(c_0_42, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.53/0.71  cnf(c_0_43, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.53/0.71  cnf(c_0_44, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.53/0.71  cnf(c_0_45, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.53/0.71  cnf(c_0_46, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.53/0.71  cnf(c_0_47, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.53/0.71  cnf(c_0_48, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_34])).
% 0.53/0.71  fof(c_0_49, plain, ![X75, X76, X77, X79, X80, X81, X82, X84]:(((~r2_hidden(X77,X76)|r2_hidden(k4_tarski(esk5_3(X75,X76,X77),X77),X75)|X76!=k2_relat_1(X75))&(~r2_hidden(k4_tarski(X80,X79),X75)|r2_hidden(X79,X76)|X76!=k2_relat_1(X75)))&((~r2_hidden(esk6_2(X81,X82),X82)|~r2_hidden(k4_tarski(X84,esk6_2(X81,X82)),X81)|X82=k2_relat_1(X81))&(r2_hidden(esk6_2(X81,X82),X82)|r2_hidden(k4_tarski(esk7_2(X81,X82),esk6_2(X81,X82)),X81)|X82=k2_relat_1(X81)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.53/0.71  cnf(c_0_50, plain, (k10_relat_1(X1,k4_xboole_0(X2,k2_relat_1(X1)))=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.53/0.71  cnf(c_0_51, negated_conjecture, (v1_relat_1(esk9_0)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.53/0.71  cnf(c_0_52, plain, (k4_xboole_0(X1,X2)=X1|~r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.53/0.71  cnf(c_0_53, plain, (r2_hidden(X1,X2)|r1_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.53/0.71  cnf(c_0_54, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.53/0.71  cnf(c_0_55, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk7_2(X1,X2),esk6_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.53/0.71  cnf(c_0_56, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(esk9_0))|k10_relat_1(esk9_0,k1_tarski(esk8_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.53/0.71  cnf(c_0_57, negated_conjecture, (k10_relat_1(esk9_0,k4_xboole_0(X1,k2_relat_1(esk9_0)))=k1_xboole_0), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.53/0.71  cnf(c_0_58, plain, (k4_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)=k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)|r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.53/0.71  cnf(c_0_59, plain, (X1=k2_relat_1(k1_xboole_0)|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.53/0.71  cnf(c_0_60, negated_conjecture, (k10_relat_1(esk9_0,k1_tarski(esk8_0))=k1_xboole_0|~r2_hidden(esk8_0,k2_relat_1(esk9_0))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.53/0.71  cnf(c_0_61, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(esk9_0))|k10_relat_1(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))!=k1_xboole_0), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.53/0.71  cnf(c_0_62, negated_conjecture, (k10_relat_1(esk9_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))=k1_xboole_0|r2_hidden(X1,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.53/0.71  fof(c_0_63, plain, ![X63, X64, X65, X66, X68, X69, X70, X71, X73]:((((r2_hidden(k4_tarski(X66,esk2_4(X63,X64,X65,X66)),X63)|~r2_hidden(X66,X65)|X65!=k10_relat_1(X63,X64)|~v1_relat_1(X63))&(r2_hidden(esk2_4(X63,X64,X65,X66),X64)|~r2_hidden(X66,X65)|X65!=k10_relat_1(X63,X64)|~v1_relat_1(X63)))&(~r2_hidden(k4_tarski(X68,X69),X63)|~r2_hidden(X69,X64)|r2_hidden(X68,X65)|X65!=k10_relat_1(X63,X64)|~v1_relat_1(X63)))&((~r2_hidden(esk3_3(X63,X70,X71),X71)|(~r2_hidden(k4_tarski(esk3_3(X63,X70,X71),X73),X63)|~r2_hidden(X73,X70))|X71=k10_relat_1(X63,X70)|~v1_relat_1(X63))&((r2_hidden(k4_tarski(esk3_3(X63,X70,X71),esk4_3(X63,X70,X71)),X63)|r2_hidden(esk3_3(X63,X70,X71),X71)|X71=k10_relat_1(X63,X70)|~v1_relat_1(X63))&(r2_hidden(esk4_3(X63,X70,X71),X70)|r2_hidden(esk3_3(X63,X70,X71),X71)|X71=k10_relat_1(X63,X70)|~v1_relat_1(X63))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.53/0.71  cnf(c_0_64, plain, (r2_hidden(k4_tarski(esk5_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.53/0.71  cnf(c_0_65, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_54, c_0_59])).
% 0.53/0.71  cnf(c_0_66, negated_conjecture, (k10_relat_1(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))=k1_xboole_0|~r2_hidden(esk8_0,k2_relat_1(esk9_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_60, c_0_40]), c_0_41]), c_0_42]), c_0_43]), c_0_44]), c_0_45]), c_0_46])).
% 0.53/0.71  cnf(c_0_67, negated_conjecture, (r2_hidden(esk8_0,k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_61, c_0_62])).
% 0.53/0.71  fof(c_0_68, plain, ![X48, X49, X50, X51, X52, X53, X54, X55, X56, X57, X58, X59, X60, X61]:(((~r2_hidden(X54,X53)|(X54=X48|X54=X49|X54=X50|X54=X51|X54=X52)|X53!=k3_enumset1(X48,X49,X50,X51,X52))&(((((X55!=X48|r2_hidden(X55,X53)|X53!=k3_enumset1(X48,X49,X50,X51,X52))&(X55!=X49|r2_hidden(X55,X53)|X53!=k3_enumset1(X48,X49,X50,X51,X52)))&(X55!=X50|r2_hidden(X55,X53)|X53!=k3_enumset1(X48,X49,X50,X51,X52)))&(X55!=X51|r2_hidden(X55,X53)|X53!=k3_enumset1(X48,X49,X50,X51,X52)))&(X55!=X52|r2_hidden(X55,X53)|X53!=k3_enumset1(X48,X49,X50,X51,X52))))&((((((esk1_6(X56,X57,X58,X59,X60,X61)!=X56|~r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)|X61=k3_enumset1(X56,X57,X58,X59,X60))&(esk1_6(X56,X57,X58,X59,X60,X61)!=X57|~r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)|X61=k3_enumset1(X56,X57,X58,X59,X60)))&(esk1_6(X56,X57,X58,X59,X60,X61)!=X58|~r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)|X61=k3_enumset1(X56,X57,X58,X59,X60)))&(esk1_6(X56,X57,X58,X59,X60,X61)!=X59|~r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)|X61=k3_enumset1(X56,X57,X58,X59,X60)))&(esk1_6(X56,X57,X58,X59,X60,X61)!=X60|~r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)|X61=k3_enumset1(X56,X57,X58,X59,X60)))&(r2_hidden(esk1_6(X56,X57,X58,X59,X60,X61),X61)|(esk1_6(X56,X57,X58,X59,X60,X61)=X56|esk1_6(X56,X57,X58,X59,X60,X61)=X57|esk1_6(X56,X57,X58,X59,X60,X61)=X58|esk1_6(X56,X57,X58,X59,X60,X61)=X59|esk1_6(X56,X57,X58,X59,X60,X61)=X60)|X61=k3_enumset1(X56,X57,X58,X59,X60)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_enumset1])])])])])])).
% 0.53/0.71  cnf(c_0_69, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.53/0.71  cnf(c_0_70, plain, (X1!=k1_xboole_0|~r2_hidden(X2,X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_54])).
% 0.53/0.71  cnf(c_0_71, plain, (r1_xboole_0(k2_relat_1(X1),X2)|k10_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.53/0.71  cnf(c_0_72, negated_conjecture, (k10_relat_1(esk9_0,k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.53/0.71  cnf(c_0_73, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k3_enumset1(X4,X5,X6,X7,X2)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.53/0.71  cnf(c_0_74, negated_conjecture, (X1!=k1_xboole_0|~r2_hidden(X2,k4_xboole_0(X3,k2_relat_1(esk9_0)))|~r2_hidden(k4_tarski(X4,X2),esk9_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_57]), c_0_51])]), c_0_70])).
% 0.53/0.71  cnf(c_0_75, plain, (r2_hidden(k4_tarski(esk5_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_64])).
% 0.53/0.71  cnf(c_0_76, negated_conjecture, (r1_xboole_0(k2_relat_1(esk9_0),k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_51])])).
% 0.53/0.71  cnf(c_0_77, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k6_enumset1(X4,X4,X4,X4,X5,X6,X7,X2)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73, c_0_44]), c_0_45]), c_0_46])).
% 0.53/0.71  cnf(c_0_78, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(X2,k2_relat_1(esk9_0)))|~r2_hidden(k4_tarski(X3,X1),esk9_0)), inference(er,[status(thm)],[c_0_74])).
% 0.53/0.71  cnf(c_0_79, negated_conjecture, (r2_hidden(k4_tarski(esk5_3(esk9_0,k2_relat_1(esk9_0),esk8_0),esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_75, c_0_67])).
% 0.53/0.71  cnf(c_0_80, negated_conjecture, (r1_xboole_0(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_relat_1(esk9_0))), inference(spm,[status(thm)],[c_0_22, c_0_76])).
% 0.53/0.71  cnf(c_0_81, plain, (r2_hidden(X1,X2)|X2!=k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X1)), inference(er,[status(thm)],[c_0_77])).
% 0.53/0.71  cnf(c_0_82, negated_conjecture, (~r2_hidden(esk8_0,k4_xboole_0(X1,k2_relat_1(esk9_0)))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.53/0.71  cnf(c_0_83, negated_conjecture, (k4_xboole_0(k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0),k2_relat_1(esk9_0))=k6_enumset1(esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0,esk8_0)), inference(spm,[status(thm)],[c_0_52, c_0_80])).
% 0.53/0.71  cnf(c_0_84, plain, (r2_hidden(X1,k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X1))), inference(er,[status(thm)],[c_0_81])).
% 0.53/0.71  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82, c_0_83]), c_0_84])]), ['proof']).
% 0.53/0.71  # SZS output end CNFRefutation
% 0.53/0.71  # Proof object total steps             : 86
% 0.53/0.71  # Proof object clause steps            : 49
% 0.53/0.71  # Proof object formula steps           : 37
% 0.53/0.71  # Proof object conjectures             : 20
% 0.53/0.71  # Proof object clause conjectures      : 17
% 0.53/0.71  # Proof object formula conjectures     : 3
% 0.53/0.71  # Proof object initial clauses used    : 22
% 0.53/0.71  # Proof object initial formulas used   : 18
% 0.53/0.71  # Proof object generating inferences   : 21
% 0.53/0.71  # Proof object simplifying inferences  : 35
% 0.53/0.71  # Training examples: 0 positive, 0 negative
% 0.53/0.71  # Parsed axioms                        : 18
% 0.53/0.71  # Removed by relevancy pruning/SinE    : 0
% 0.53/0.71  # Initial clauses                      : 43
% 0.53/0.71  # Removed in clause preprocessing      : 7
% 0.53/0.71  # Initial clauses in saturation        : 36
% 0.53/0.71  # Processed clauses                    : 559
% 0.53/0.71  # ...of these trivial                  : 3
% 0.53/0.71  # ...subsumed                          : 253
% 0.53/0.71  # ...remaining for further processing  : 303
% 0.53/0.71  # Other redundant clauses eliminated   : 287
% 0.53/0.71  # Clauses deleted for lack of memory   : 0
% 0.53/0.71  # Backward-subsumed                    : 7
% 0.53/0.71  # Backward-rewritten                   : 37
% 0.53/0.71  # Generated clauses                    : 5810
% 0.53/0.71  # ...of the previous two non-trivial   : 5327
% 0.53/0.71  # Contextual simplify-reflections      : 1
% 0.53/0.71  # Paramodulations                      : 5365
% 0.53/0.71  # Factorizations                       : 54
% 0.53/0.71  # Equation resolutions                 : 384
% 0.53/0.71  # Propositional unsat checks           : 0
% 0.53/0.71  #    Propositional check models        : 0
% 0.53/0.71  #    Propositional check unsatisfiable : 0
% 0.53/0.71  #    Propositional clauses             : 0
% 0.53/0.71  #    Propositional clauses after purity: 0
% 0.53/0.71  #    Propositional unsat core size     : 0
% 0.53/0.71  #    Propositional preprocessing time  : 0.000
% 0.53/0.71  #    Propositional encoding time       : 0.000
% 0.53/0.71  #    Propositional solver time         : 0.000
% 0.53/0.71  #    Success case prop preproc time    : 0.000
% 0.53/0.71  #    Success case prop encoding time   : 0.000
% 0.53/0.71  #    Success case prop solver time     : 0.000
% 0.53/0.71  # Current number of processed clauses  : 247
% 0.53/0.71  #    Positive orientable unit clauses  : 33
% 0.53/0.71  #    Positive unorientable unit clauses: 0
% 0.53/0.71  #    Negative unit clauses             : 10
% 0.53/0.71  #    Non-unit-clauses                  : 204
% 0.53/0.71  # Current number of unprocessed clauses: 4750
% 0.53/0.71  # ...number of literals in the above   : 61498
% 0.53/0.71  # Current number of archived formulas  : 0
% 0.53/0.71  # Current number of archived clauses   : 58
% 0.53/0.71  # Clause-clause subsumption calls (NU) : 14574
% 0.53/0.71  # Rec. Clause-clause subsumption calls : 6321
% 0.53/0.71  # Non-unit clause-clause subsumptions  : 189
% 0.53/0.71  # Unit Clause-clause subsumption calls : 945
% 0.53/0.71  # Rewrite failures with RHS unbound    : 0
% 0.53/0.71  # BW rewrite match attempts            : 38
% 0.53/0.71  # BW rewrite match successes           : 4
% 0.53/0.71  # Condensation attempts                : 0
% 0.53/0.71  # Condensation successes               : 0
% 0.53/0.71  # Termbank termtop insertions          : 199417
% 0.53/0.71  
% 0.53/0.71  # -------------------------------------------------
% 0.53/0.71  # User time                : 0.353 s
% 0.53/0.71  # System time              : 0.009 s
% 0.53/0.71  # Total time               : 0.362 s
% 0.53/0.71  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
