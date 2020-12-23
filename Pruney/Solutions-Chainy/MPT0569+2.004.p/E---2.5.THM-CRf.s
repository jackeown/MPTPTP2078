%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:33 EST 2020

% Result     : Theorem 0.44s
% Output     : CNFRefutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 109 expanded)
%              Number of clauses        :   28 (  48 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 416 expanded)
%              Number of equality atoms :   30 (  67 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

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

fof(t143_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k9_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k1_relat_1(X3))
            & r2_hidden(k4_tarski(X4,X1),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(t146_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(c_0_10,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_11,plain,(
    ! [X44,X45,X46,X48] :
      ( ( r2_hidden(esk9_3(X44,X45,X46),k2_relat_1(X46))
        | ~ r2_hidden(X44,k10_relat_1(X46,X45))
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(k4_tarski(X44,esk9_3(X44,X45,X46)),X46)
        | ~ r2_hidden(X44,k10_relat_1(X46,X45))
        | ~ v1_relat_1(X46) )
      & ( r2_hidden(esk9_3(X44,X45,X46),X45)
        | ~ r2_hidden(X44,k10_relat_1(X46,X45))
        | ~ v1_relat_1(X46) )
      & ( ~ r2_hidden(X48,k2_relat_1(X46))
        | ~ r2_hidden(k4_tarski(X44,X48),X46)
        | ~ r2_hidden(X48,X45)
        | r2_hidden(X44,k10_relat_1(X46,X45))
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

fof(c_0_12,plain,(
    ! [X13,X14] :
      ( ~ r1_xboole_0(k1_tarski(X13),X14)
      | ~ r2_hidden(X13,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_13,plain,(
    ! [X12] : r1_xboole_0(X12,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X27,X28,X29,X31,X32,X33,X34,X36] :
      ( ( ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,esk5_3(X27,X28,X29)),X27)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(X31,X32),X27)
        | r2_hidden(X31,X28)
        | X28 != k1_relat_1(X27) )
      & ( ~ r2_hidden(esk6_2(X33,X34),X34)
        | ~ r2_hidden(k4_tarski(esk6_2(X33,X34),X36),X33)
        | X34 = k1_relat_1(X33) )
      & ( r2_hidden(esk6_2(X33,X34),X34)
        | r2_hidden(k4_tarski(esk6_2(X33,X34),esk7_2(X33,X34)),X33)
        | X34 = k1_relat_1(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_19,plain,(
    ! [X15,X16,X17,X18,X20,X21,X22,X23,X25] :
      ( ( r2_hidden(k4_tarski(X18,esk2_4(X15,X16,X17,X18)),X15)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk2_4(X15,X16,X17,X18),X16)
        | ~ r2_hidden(X18,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),X15)
        | ~ r2_hidden(X21,X16)
        | r2_hidden(X20,X17)
        | X17 != k10_relat_1(X15,X16)
        | ~ v1_relat_1(X15) )
      & ( ~ r2_hidden(esk3_3(X15,X22,X23),X23)
        | ~ r2_hidden(k4_tarski(esk3_3(X15,X22,X23),X25),X15)
        | ~ r2_hidden(X25,X22)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(k4_tarski(esk3_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)
        | r2_hidden(esk3_3(X15,X22,X23),X23)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) )
      & ( r2_hidden(esk4_3(X15,X22,X23),X22)
        | r2_hidden(esk3_3(X15,X22,X23),X23)
        | X23 = k10_relat_1(X15,X22)
        | ~ v1_relat_1(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

fof(c_0_20,plain,(
    ! [X38,X39,X40,X42] :
      ( ( r2_hidden(esk8_3(X38,X39,X40),k1_relat_1(X40))
        | ~ r2_hidden(X38,k9_relat_1(X40,X39))
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(k4_tarski(esk8_3(X38,X39,X40),X38),X40)
        | ~ r2_hidden(X38,k9_relat_1(X40,X39))
        | ~ v1_relat_1(X40) )
      & ( r2_hidden(esk8_3(X38,X39,X40),X39)
        | ~ r2_hidden(X38,k9_relat_1(X40,X39))
        | ~ v1_relat_1(X40) )
      & ( ~ r2_hidden(X42,k1_relat_1(X40))
        | ~ r2_hidden(k4_tarski(X42,X38),X40)
        | ~ r2_hidden(X42,X39)
        | r2_hidden(X38,k9_relat_1(X40,X39))
        | ~ v1_relat_1(X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).

cnf(c_0_21,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(esk9_3(X2,X3,X1),X4)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(X4,X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(esk9_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_26,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(k4_tarski(esk8_3(X1,X2,X3),X1),X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k10_relat_1(X1,X3))
    | ~ r1_xboole_0(k2_relat_1(X1),X3) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk6_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

fof(c_0_31,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & ( k10_relat_1(esk11_0,esk10_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) )
    & ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).

cnf(c_0_32,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),X4)
    | X4 != k10_relat_1(X3,X5)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ r2_hidden(X1,X5) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k2_relat_1(X1),X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_35,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_36,plain,
    ( r2_hidden(esk8_3(X1,X2,X3),k10_relat_1(X3,X4))
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k9_relat_1(X3,X2))
    | ~ r2_hidden(X1,X4) ),
    inference(er,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

fof(c_0_38,plain,(
    ! [X43] :
      ( ~ v1_relat_1(X43)
      | k9_relat_1(X43,k1_relat_1(X43)) = k2_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).

cnf(c_0_39,negated_conjecture,
    ( ~ r2_hidden(X1,k9_relat_1(esk11_0,X2))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_35])]),c_0_23])).

cnf(c_0_40,plain,
    ( k9_relat_1(X1,k1_relat_1(X1)) = k2_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_41,negated_conjecture,
    ( ~ r2_hidden(X1,k2_relat_1(esk11_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_35])])).

cnf(c_0_42,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,negated_conjecture,
    ( k10_relat_1(esk11_0,esk10_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(X1,esk10_0)
    | ~ r2_hidden(esk1_2(X1,esk10_0),k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk11_0),esk10_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_37])])).

cnf(c_0_47,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.06/0.26  % Computer   : n011.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % WCLimit    : 600
% 0.06/0.26  % DateTime   : Tue Dec  1 20:21:41 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  # Version: 2.5pre002
% 0.06/0.26  # No SInE strategy applied
% 0.06/0.26  # Trying AutoSched0 for 299 seconds
% 0.44/0.61  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.44/0.61  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.44/0.61  #
% 0.44/0.61  # Preprocessing time       : 0.013 s
% 0.44/0.61  # Presaturation interreduction done
% 0.44/0.61  
% 0.44/0.61  # Proof found!
% 0.44/0.61  # SZS status Theorem
% 0.44/0.61  # SZS output start CNFRefutation
% 0.44/0.61  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.44/0.61  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 0.44/0.61  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.44/0.61  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.44/0.61  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.44/0.61  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 0.44/0.61  fof(t143_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k9_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k1_relat_1(X3))&r2_hidden(k4_tarski(X4,X1),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 0.44/0.61  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.44/0.61  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 0.44/0.61  fof(t146_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 0.44/0.61  fof(c_0_10, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.44/0.61  fof(c_0_11, plain, ![X44, X45, X46, X48]:((((r2_hidden(esk9_3(X44,X45,X46),k2_relat_1(X46))|~r2_hidden(X44,k10_relat_1(X46,X45))|~v1_relat_1(X46))&(r2_hidden(k4_tarski(X44,esk9_3(X44,X45,X46)),X46)|~r2_hidden(X44,k10_relat_1(X46,X45))|~v1_relat_1(X46)))&(r2_hidden(esk9_3(X44,X45,X46),X45)|~r2_hidden(X44,k10_relat_1(X46,X45))|~v1_relat_1(X46)))&(~r2_hidden(X48,k2_relat_1(X46))|~r2_hidden(k4_tarski(X44,X48),X46)|~r2_hidden(X48,X45)|r2_hidden(X44,k10_relat_1(X46,X45))|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.44/0.61  fof(c_0_12, plain, ![X13, X14]:(~r1_xboole_0(k1_tarski(X13),X14)|~r2_hidden(X13,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.44/0.61  fof(c_0_13, plain, ![X12]:r1_xboole_0(X12,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.44/0.61  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.44/0.61  cnf(c_0_15, plain, (r2_hidden(esk9_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.44/0.61  cnf(c_0_16, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.44/0.61  cnf(c_0_17, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.44/0.61  fof(c_0_18, plain, ![X27, X28, X29, X31, X32, X33, X34, X36]:(((~r2_hidden(X29,X28)|r2_hidden(k4_tarski(X29,esk5_3(X27,X28,X29)),X27)|X28!=k1_relat_1(X27))&(~r2_hidden(k4_tarski(X31,X32),X27)|r2_hidden(X31,X28)|X28!=k1_relat_1(X27)))&((~r2_hidden(esk6_2(X33,X34),X34)|~r2_hidden(k4_tarski(esk6_2(X33,X34),X36),X33)|X34=k1_relat_1(X33))&(r2_hidden(esk6_2(X33,X34),X34)|r2_hidden(k4_tarski(esk6_2(X33,X34),esk7_2(X33,X34)),X33)|X34=k1_relat_1(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.44/0.61  fof(c_0_19, plain, ![X15, X16, X17, X18, X20, X21, X22, X23, X25]:((((r2_hidden(k4_tarski(X18,esk2_4(X15,X16,X17,X18)),X15)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15))&(r2_hidden(esk2_4(X15,X16,X17,X18),X16)|~r2_hidden(X18,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15)))&(~r2_hidden(k4_tarski(X20,X21),X15)|~r2_hidden(X21,X16)|r2_hidden(X20,X17)|X17!=k10_relat_1(X15,X16)|~v1_relat_1(X15)))&((~r2_hidden(esk3_3(X15,X22,X23),X23)|(~r2_hidden(k4_tarski(esk3_3(X15,X22,X23),X25),X15)|~r2_hidden(X25,X22))|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))&((r2_hidden(k4_tarski(esk3_3(X15,X22,X23),esk4_3(X15,X22,X23)),X15)|r2_hidden(esk3_3(X15,X22,X23),X23)|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))&(r2_hidden(esk4_3(X15,X22,X23),X22)|r2_hidden(esk3_3(X15,X22,X23),X23)|X23=k10_relat_1(X15,X22)|~v1_relat_1(X15))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.44/0.61  fof(c_0_20, plain, ![X38, X39, X40, X42]:((((r2_hidden(esk8_3(X38,X39,X40),k1_relat_1(X40))|~r2_hidden(X38,k9_relat_1(X40,X39))|~v1_relat_1(X40))&(r2_hidden(k4_tarski(esk8_3(X38,X39,X40),X38),X40)|~r2_hidden(X38,k9_relat_1(X40,X39))|~v1_relat_1(X40)))&(r2_hidden(esk8_3(X38,X39,X40),X39)|~r2_hidden(X38,k9_relat_1(X40,X39))|~v1_relat_1(X40)))&(~r2_hidden(X42,k1_relat_1(X40))|~r2_hidden(k4_tarski(X42,X38),X40)|~r2_hidden(X42,X39)|r2_hidden(X38,k9_relat_1(X40,X39))|~v1_relat_1(X40))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t143_relat_1])])])])])).
% 0.44/0.61  cnf(c_0_21, plain, (~v1_relat_1(X1)|~r2_hidden(esk9_3(X2,X3,X1),X4)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(X4,X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.44/0.61  cnf(c_0_22, plain, (r2_hidden(esk9_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.44/0.61  cnf(c_0_23, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.44/0.61  cnf(c_0_24, plain, (r2_hidden(esk6_2(X1,X2),X2)|r2_hidden(k4_tarski(esk6_2(X1,X2),esk7_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.44/0.61  cnf(c_0_25, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.44/0.61  fof(c_0_26, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.44/0.61  cnf(c_0_27, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.44/0.61  cnf(c_0_28, plain, (r2_hidden(k4_tarski(esk8_3(X1,X2,X3),X1),X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.44/0.61  cnf(c_0_29, plain, (~v1_relat_1(X1)|~r2_hidden(X2,k10_relat_1(X1,X3))|~r1_xboole_0(k2_relat_1(X1),X3)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.44/0.61  cnf(c_0_30, plain, (X1=k1_xboole_0|r2_hidden(esk6_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.44/0.61  fof(c_0_31, negated_conjecture, (v1_relat_1(esk11_0)&((k10_relat_1(esk11_0,esk10_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk11_0),esk10_0))&(k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk11_0),esk10_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_26])])])).
% 0.44/0.61  cnf(c_0_32, plain, (r2_hidden(esk8_3(X1,X2,X3),X4)|X4!=k10_relat_1(X3,X5)|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~r2_hidden(X1,X5)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.44/0.61  cnf(c_0_33, plain, (k10_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k2_relat_1(X1),X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.44/0.61  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.44/0.61  cnf(c_0_35, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.44/0.62  cnf(c_0_36, plain, (r2_hidden(esk8_3(X1,X2,X3),k10_relat_1(X3,X4))|~v1_relat_1(X3)|~r2_hidden(X1,k9_relat_1(X3,X2))|~r2_hidden(X1,X4)), inference(er,[status(thm)],[c_0_32])).
% 0.44/0.62  cnf(c_0_37, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35])])).
% 0.44/0.62  fof(c_0_38, plain, ![X43]:(~v1_relat_1(X43)|k9_relat_1(X43,k1_relat_1(X43))=k2_relat_1(X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t146_relat_1])])).
% 0.44/0.62  cnf(c_0_39, negated_conjecture, (~r2_hidden(X1,k9_relat_1(esk11_0,X2))|~r2_hidden(X1,esk10_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_35])]), c_0_23])).
% 0.44/0.62  cnf(c_0_40, plain, (k9_relat_1(X1,k1_relat_1(X1))=k2_relat_1(X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.44/0.62  cnf(c_0_41, negated_conjecture, (~r2_hidden(X1,k2_relat_1(esk11_0))|~r2_hidden(X1,esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_35])])).
% 0.44/0.62  cnf(c_0_42, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.44/0.62  cnf(c_0_43, negated_conjecture, (k10_relat_1(esk11_0,esk10_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.44/0.62  cnf(c_0_44, negated_conjecture, (r1_xboole_0(X1,esk10_0)|~r2_hidden(esk1_2(X1,esk10_0),k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.44/0.62  cnf(c_0_45, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.44/0.62  cnf(c_0_46, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk11_0),esk10_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_37])])).
% 0.44/0.62  cnf(c_0_47, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), ['proof']).
% 0.44/0.62  # SZS output end CNFRefutation
% 0.44/0.62  # Proof object total steps             : 48
% 0.44/0.62  # Proof object clause steps            : 28
% 0.44/0.62  # Proof object formula steps           : 20
% 0.44/0.62  # Proof object conjectures             : 12
% 0.44/0.62  # Proof object clause conjectures      : 9
% 0.44/0.62  # Proof object formula conjectures     : 3
% 0.44/0.62  # Proof object initial clauses used    : 15
% 0.44/0.62  # Proof object initial formulas used   : 10
% 0.44/0.62  # Proof object generating inferences   : 12
% 0.44/0.62  # Proof object simplifying inferences  : 11
% 0.44/0.62  # Training examples: 0 positive, 0 negative
% 0.44/0.62  # Parsed axioms                        : 10
% 0.44/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.44/0.62  # Initial clauses                      : 29
% 0.44/0.62  # Removed in clause preprocessing      : 0
% 0.44/0.62  # Initial clauses in saturation        : 29
% 0.44/0.62  # Processed clauses                    : 4561
% 0.44/0.62  # ...of these trivial                  : 4
% 0.44/0.62  # ...subsumed                          : 3849
% 0.44/0.62  # ...remaining for further processing  : 708
% 0.44/0.62  # Other redundant clauses eliminated   : 0
% 0.44/0.62  # Clauses deleted for lack of memory   : 0
% 0.44/0.62  # Backward-subsumed                    : 5
% 0.44/0.62  # Backward-rewritten                   : 9
% 0.44/0.62  # Generated clauses                    : 33168
% 0.44/0.62  # ...of the previous two non-trivial   : 32189
% 0.44/0.62  # Contextual simplify-reflections      : 3
% 0.44/0.62  # Paramodulations                      : 33014
% 0.44/0.62  # Factorizations                       : 0
% 0.44/0.62  # Equation resolutions                 : 154
% 0.44/0.62  # Propositional unsat checks           : 0
% 0.44/0.62  #    Propositional check models        : 0
% 0.44/0.62  #    Propositional check unsatisfiable : 0
% 0.44/0.62  #    Propositional clauses             : 0
% 0.44/0.62  #    Propositional clauses after purity: 0
% 0.44/0.62  #    Propositional unsat core size     : 0
% 0.44/0.62  #    Propositional preprocessing time  : 0.000
% 0.44/0.62  #    Propositional encoding time       : 0.000
% 0.44/0.62  #    Propositional solver time         : 0.000
% 0.44/0.62  #    Success case prop preproc time    : 0.000
% 0.44/0.62  #    Success case prop encoding time   : 0.000
% 0.44/0.62  #    Success case prop solver time     : 0.000
% 0.44/0.62  # Current number of processed clauses  : 665
% 0.44/0.62  #    Positive orientable unit clauses  : 6
% 0.44/0.62  #    Positive unorientable unit clauses: 0
% 0.44/0.62  #    Negative unit clauses             : 9
% 0.44/0.62  #    Non-unit-clauses                  : 650
% 0.44/0.62  # Current number of unprocessed clauses: 27676
% 0.44/0.62  # ...number of literals in the above   : 150630
% 0.44/0.62  # Current number of archived formulas  : 0
% 0.44/0.62  # Current number of archived clauses   : 43
% 0.44/0.62  # Clause-clause subsumption calls (NU) : 189214
% 0.44/0.62  # Rec. Clause-clause subsumption calls : 54355
% 0.44/0.62  # Non-unit clause-clause subsumptions  : 2940
% 0.44/0.62  # Unit Clause-clause subsumption calls : 125
% 0.44/0.62  # Rewrite failures with RHS unbound    : 0
% 0.44/0.62  # BW rewrite match attempts            : 1
% 0.44/0.62  # BW rewrite match successes           : 1
% 0.44/0.62  # Condensation attempts                : 0
% 0.44/0.62  # Condensation successes               : 0
% 0.44/0.62  # Termbank termtop insertions          : 445683
% 0.44/0.62  
% 0.44/0.62  # -------------------------------------------------
% 0.44/0.62  # User time                : 0.338 s
% 0.44/0.62  # System time              : 0.021 s
% 0.44/0.62  # Total time               : 0.359 s
% 0.44/0.62  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
