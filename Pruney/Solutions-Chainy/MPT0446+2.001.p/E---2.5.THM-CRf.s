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
% DateTime   : Thu Dec  3 10:48:20 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 190 expanded)
%              Number of clauses        :   33 (  77 expanded)
%              Number of leaves         :   14 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  120 ( 298 expanded)
%              Number of equality atoms :   43 ( 150 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l51_zfmisc_1,axiom,(
    ! [X1,X2] : k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(t72_enumset1,axiom,(
    ! [X1,X2,X3,X4] : k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(t73_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5] : k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(t74_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6] : k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(t75_enumset1,axiom,(
    ! [X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(t30_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X1,X2),X3)
       => ( r2_hidden(X1,k3_relat_1(X3))
          & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_14,plain,(
    ! [X54,X55] : k3_tarski(k2_tarski(X54,X55)) = k2_xboole_0(X54,X55) ),
    inference(variable_rename,[status(thm)],[l51_zfmisc_1])).

fof(c_0_15,plain,(
    ! [X18,X19] : k1_enumset1(X18,X18,X19) = k2_tarski(X18,X19) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

fof(c_0_16,plain,(
    ! [X79] :
      ( ~ v1_relat_1(X79)
      | k3_relat_1(X79) = k2_xboole_0(k1_relat_1(X79),k2_relat_1(X79)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

cnf(c_0_17,plain,
    ( k3_tarski(k2_tarski(X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X20,X21,X22] : k2_enumset1(X20,X20,X21,X22) = k1_enumset1(X20,X21,X22) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

fof(c_0_20,plain,(
    ! [X23,X24,X25,X26] : k3_enumset1(X23,X23,X24,X25,X26) = k2_enumset1(X23,X24,X25,X26) ),
    inference(variable_rename,[status(thm)],[t72_enumset1])).

fof(c_0_21,plain,(
    ! [X27,X28,X29,X30,X31] : k4_enumset1(X27,X27,X28,X29,X30,X31) = k3_enumset1(X27,X28,X29,X30,X31) ),
    inference(variable_rename,[status(thm)],[t73_enumset1])).

fof(c_0_22,plain,(
    ! [X32,X33,X34,X35,X36,X37] : k5_enumset1(X32,X32,X33,X34,X35,X36,X37) = k4_enumset1(X32,X33,X34,X35,X36,X37) ),
    inference(variable_rename,[status(thm)],[t74_enumset1])).

fof(c_0_23,plain,(
    ! [X38,X39,X40,X41,X42,X43,X44] : k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44) = k5_enumset1(X38,X39,X40,X41,X42,X43,X44) ),
    inference(variable_rename,[status(thm)],[t75_enumset1])).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( r2_hidden(k4_tarski(X1,X2),X3)
         => ( r2_hidden(X1,k3_relat_1(X3))
            & r2_hidden(X2,k3_relat_1(X3)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t30_relat_1])).

fof(c_0_25,plain,(
    ! [X14,X15] : r1_tarski(X14,k2_xboole_0(X14,X15)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_26,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,plain,
    ( k3_tarski(k1_enumset1(X1,X1,X2)) = k2_xboole_0(X1,X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_28,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( k3_enumset1(X1,X1,X2,X3,X4) = k2_enumset1(X1,X2,X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k4_enumset1(X1,X1,X2,X3,X4,X5) = k3_enumset1(X1,X2,X3,X4,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k5_enumset1(X1,X1,X2,X3,X4,X5,X6) = k4_enumset1(X1,X2,X3,X4,X5,X6) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7) = k5_enumset1(X1,X2,X3,X4,X5,X6,X7) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_33,negated_conjecture,
    ( v1_relat_1(esk11_0)
    & r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)
    & ( ~ r2_hidden(esk9_0,k3_relat_1(esk11_0))
      | ~ r2_hidden(esk10_0,k3_relat_1(esk11_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).

fof(c_0_34,plain,(
    ! [X16,X17] : k2_tarski(X16,X17) = k2_tarski(X17,X16) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( k3_relat_1(X1) = k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( v1_relat_1(esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_38,plain,(
    ! [X57,X58,X59,X61,X62,X63,X64,X66] :
      ( ( ~ r2_hidden(X59,X58)
        | r2_hidden(k4_tarski(X59,esk3_3(X57,X58,X59)),X57)
        | X58 != k1_relat_1(X57) )
      & ( ~ r2_hidden(k4_tarski(X61,X62),X57)
        | r2_hidden(X61,X58)
        | X58 != k1_relat_1(X57) )
      & ( ~ r2_hidden(esk4_2(X63,X64),X64)
        | ~ r2_hidden(k4_tarski(esk4_2(X63,X64),X66),X63)
        | X64 = k1_relat_1(X63) )
      & ( r2_hidden(esk4_2(X63,X64),X64)
        | r2_hidden(k4_tarski(esk4_2(X63,X64),esk5_2(X63,X64)),X63)
        | X64 = k1_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

fof(c_0_40,plain,(
    ! [X8,X9,X10,X11,X12] :
      ( ( ~ r1_tarski(X8,X9)
        | ~ r2_hidden(X10,X8)
        | r2_hidden(X10,X9) )
      & ( r2_hidden(esk1_2(X11,X12),X11)
        | r1_tarski(X11,X12) )
      & ( ~ r2_hidden(esk1_2(X11,X12),X12)
        | r1_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_41,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_27]),c_0_28]),c_0_29]),c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_42,negated_conjecture,
    ( k3_tarski(k6_enumset1(k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k2_relat_1(esk11_0))) = k3_relat_1(esk11_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_18]),c_0_18]),c_0_28]),c_0_28]),c_0_29]),c_0_29]),c_0_30]),c_0_30]),c_0_31]),c_0_31]),c_0_32]),c_0_32])).

fof(c_0_45,plain,(
    ! [X68,X69,X70,X72,X73,X74,X75,X77] :
      ( ( ~ r2_hidden(X70,X69)
        | r2_hidden(k4_tarski(esk6_3(X68,X69,X70),X70),X68)
        | X69 != k2_relat_1(X68) )
      & ( ~ r2_hidden(k4_tarski(X73,X72),X68)
        | r2_hidden(X72,X69)
        | X69 != k2_relat_1(X68) )
      & ( ~ r2_hidden(esk7_2(X74,X75),X75)
        | ~ r2_hidden(k4_tarski(X77,esk7_2(X74,X75)),X74)
        | X75 = k2_relat_1(X74) )
      & ( r2_hidden(esk7_2(X74,X75),X75)
        | r2_hidden(k4_tarski(esk8_2(X74,X75),esk7_2(X74,X75)),X74)
        | X75 = k2_relat_1(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk11_0),k3_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_50,plain,
    ( r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk11_0))
    | ~ r2_hidden(X1,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk9_0,k1_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk11_0),k3_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_42])).

cnf(c_0_55,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k3_relat_1(esk11_0))
    | ~ r2_hidden(esk10_0,k3_relat_1(esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk9_0,k3_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk11_0))
    | ~ r2_hidden(X1,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r2_hidden(esk10_0,k2_relat_1(esk11_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_hidden(esk10_0,k3_relat_1(esk11_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_57])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:50:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.83/2.05  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 1.83/2.05  # and selection function SelectNegativeLiterals.
% 1.83/2.05  #
% 1.83/2.05  # Preprocessing time       : 0.028 s
% 1.83/2.05  # Presaturation interreduction done
% 1.83/2.05  
% 1.83/2.05  # Proof found!
% 1.83/2.05  # SZS status Theorem
% 1.83/2.05  # SZS output start CNFRefutation
% 1.83/2.05  fof(l51_zfmisc_1, axiom, ![X1, X2]:k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.83/2.05  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.83/2.05  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.83/2.05  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.83/2.05  fof(t72_enumset1, axiom, ![X1, X2, X3, X4]:k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 1.83/2.05  fof(t73_enumset1, axiom, ![X1, X2, X3, X4, X5]:k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 1.83/2.05  fof(t74_enumset1, axiom, ![X1, X2, X3, X4, X5, X6]:k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 1.83/2.05  fof(t75_enumset1, axiom, ![X1, X2, X3, X4, X5, X6, X7]:k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 1.83/2.05  fof(t30_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 1.83/2.05  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.83/2.05  fof(commutativity_k2_tarski, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_tarski(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.83/2.05  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.83/2.05  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.83/2.05  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.83/2.05  fof(c_0_14, plain, ![X54, X55]:k3_tarski(k2_tarski(X54,X55))=k2_xboole_0(X54,X55), inference(variable_rename,[status(thm)],[l51_zfmisc_1])).
% 1.83/2.05  fof(c_0_15, plain, ![X18, X19]:k1_enumset1(X18,X18,X19)=k2_tarski(X18,X19), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 1.83/2.05  fof(c_0_16, plain, ![X79]:(~v1_relat_1(X79)|k3_relat_1(X79)=k2_xboole_0(k1_relat_1(X79),k2_relat_1(X79))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 1.83/2.05  cnf(c_0_17, plain, (k3_tarski(k2_tarski(X1,X2))=k2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.83/2.05  cnf(c_0_18, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 1.83/2.05  fof(c_0_19, plain, ![X20, X21, X22]:k2_enumset1(X20,X20,X21,X22)=k1_enumset1(X20,X21,X22), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 1.83/2.05  fof(c_0_20, plain, ![X23, X24, X25, X26]:k3_enumset1(X23,X23,X24,X25,X26)=k2_enumset1(X23,X24,X25,X26), inference(variable_rename,[status(thm)],[t72_enumset1])).
% 1.83/2.05  fof(c_0_21, plain, ![X27, X28, X29, X30, X31]:k4_enumset1(X27,X27,X28,X29,X30,X31)=k3_enumset1(X27,X28,X29,X30,X31), inference(variable_rename,[status(thm)],[t73_enumset1])).
% 1.83/2.05  fof(c_0_22, plain, ![X32, X33, X34, X35, X36, X37]:k5_enumset1(X32,X32,X33,X34,X35,X36,X37)=k4_enumset1(X32,X33,X34,X35,X36,X37), inference(variable_rename,[status(thm)],[t74_enumset1])).
% 1.83/2.05  fof(c_0_23, plain, ![X38, X39, X40, X41, X42, X43, X44]:k6_enumset1(X38,X38,X39,X40,X41,X42,X43,X44)=k5_enumset1(X38,X39,X40,X41,X42,X43,X44), inference(variable_rename,[status(thm)],[t75_enumset1])).
% 1.83/2.05  fof(c_0_24, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(k4_tarski(X1,X2),X3)=>(r2_hidden(X1,k3_relat_1(X3))&r2_hidden(X2,k3_relat_1(X3)))))), inference(assume_negation,[status(cth)],[t30_relat_1])).
% 1.83/2.05  fof(c_0_25, plain, ![X14, X15]:r1_tarski(X14,k2_xboole_0(X14,X15)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 1.83/2.05  cnf(c_0_26, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 1.83/2.05  cnf(c_0_27, plain, (k3_tarski(k1_enumset1(X1,X1,X2))=k2_xboole_0(X1,X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 1.83/2.05  cnf(c_0_28, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.83/2.05  cnf(c_0_29, plain, (k3_enumset1(X1,X1,X2,X3,X4)=k2_enumset1(X1,X2,X3,X4)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 1.83/2.05  cnf(c_0_30, plain, (k4_enumset1(X1,X1,X2,X3,X4,X5)=k3_enumset1(X1,X2,X3,X4,X5)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 1.83/2.05  cnf(c_0_31, plain, (k5_enumset1(X1,X1,X2,X3,X4,X5,X6)=k4_enumset1(X1,X2,X3,X4,X5,X6)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 1.83/2.05  cnf(c_0_32, plain, (k6_enumset1(X1,X1,X2,X3,X4,X5,X6,X7)=k5_enumset1(X1,X2,X3,X4,X5,X6,X7)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 1.83/2.05  fof(c_0_33, negated_conjecture, (v1_relat_1(esk11_0)&(r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)&(~r2_hidden(esk9_0,k3_relat_1(esk11_0))|~r2_hidden(esk10_0,k3_relat_1(esk11_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_24])])])).
% 1.83/2.05  fof(c_0_34, plain, ![X16, X17]:k2_tarski(X16,X17)=k2_tarski(X17,X16), inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).
% 1.83/2.05  cnf(c_0_35, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 1.83/2.05  cnf(c_0_36, plain, (k3_relat_1(X1)=k3_tarski(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k2_relat_1(X1)))|~v1_relat_1(X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.83/2.05  cnf(c_0_37, negated_conjecture, (v1_relat_1(esk11_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.83/2.05  fof(c_0_38, plain, ![X57, X58, X59, X61, X62, X63, X64, X66]:(((~r2_hidden(X59,X58)|r2_hidden(k4_tarski(X59,esk3_3(X57,X58,X59)),X57)|X58!=k1_relat_1(X57))&(~r2_hidden(k4_tarski(X61,X62),X57)|r2_hidden(X61,X58)|X58!=k1_relat_1(X57)))&((~r2_hidden(esk4_2(X63,X64),X64)|~r2_hidden(k4_tarski(esk4_2(X63,X64),X66),X63)|X64=k1_relat_1(X63))&(r2_hidden(esk4_2(X63,X64),X64)|r2_hidden(k4_tarski(esk4_2(X63,X64),esk5_2(X63,X64)),X63)|X64=k1_relat_1(X63)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.83/2.05  cnf(c_0_39, plain, (k2_tarski(X1,X2)=k2_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 1.83/2.05  fof(c_0_40, plain, ![X8, X9, X10, X11, X12]:((~r1_tarski(X8,X9)|(~r2_hidden(X10,X8)|r2_hidden(X10,X9)))&((r2_hidden(esk1_2(X11,X12),X11)|r1_tarski(X11,X12))&(~r2_hidden(esk1_2(X11,X12),X12)|r1_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 1.83/2.05  cnf(c_0_41, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_35, c_0_27]), c_0_28]), c_0_29]), c_0_30]), c_0_31]), c_0_32])).
% 1.83/2.05  cnf(c_0_42, negated_conjecture, (k3_tarski(k6_enumset1(k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k1_relat_1(esk11_0),k2_relat_1(esk11_0)))=k3_relat_1(esk11_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 1.83/2.05  cnf(c_0_43, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 1.83/2.05  cnf(c_0_44, plain, (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)=k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_18]), c_0_18]), c_0_28]), c_0_28]), c_0_29]), c_0_29]), c_0_30]), c_0_30]), c_0_31]), c_0_31]), c_0_32]), c_0_32])).
% 1.83/2.05  fof(c_0_45, plain, ![X68, X69, X70, X72, X73, X74, X75, X77]:(((~r2_hidden(X70,X69)|r2_hidden(k4_tarski(esk6_3(X68,X69,X70),X70),X68)|X69!=k2_relat_1(X68))&(~r2_hidden(k4_tarski(X73,X72),X68)|r2_hidden(X72,X69)|X69!=k2_relat_1(X68)))&((~r2_hidden(esk7_2(X74,X75),X75)|~r2_hidden(k4_tarski(X77,esk7_2(X74,X75)),X74)|X75=k2_relat_1(X74))&(r2_hidden(esk7_2(X74,X75),X75)|r2_hidden(k4_tarski(esk8_2(X74,X75),esk7_2(X74,X75)),X74)|X75=k2_relat_1(X74)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.83/2.05  cnf(c_0_46, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 1.83/2.05  cnf(c_0_47, negated_conjecture, (r1_tarski(k1_relat_1(esk11_0),k3_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.83/2.05  cnf(c_0_48, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_43])).
% 1.83/2.05  cnf(c_0_49, negated_conjecture, (r2_hidden(k4_tarski(esk9_0,esk10_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.83/2.05  cnf(c_0_50, plain, (r1_tarski(X1,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))), inference(spm,[status(thm)],[c_0_41, c_0_44])).
% 1.83/2.05  cnf(c_0_51, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 1.83/2.05  cnf(c_0_52, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk11_0))|~r2_hidden(X1,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 1.83/2.05  cnf(c_0_53, negated_conjecture, (r2_hidden(esk9_0,k1_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 1.83/2.05  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_relat_1(esk11_0),k3_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_50, c_0_42])).
% 1.83/2.05  cnf(c_0_55, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_51])).
% 1.83/2.05  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk9_0,k3_relat_1(esk11_0))|~r2_hidden(esk10_0,k3_relat_1(esk11_0))), inference(split_conjunct,[status(thm)],[c_0_33])).
% 1.83/2.05  cnf(c_0_57, negated_conjecture, (r2_hidden(esk9_0,k3_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 1.83/2.05  cnf(c_0_58, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk11_0))|~r2_hidden(X1,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_46, c_0_54])).
% 1.83/2.05  cnf(c_0_59, negated_conjecture, (r2_hidden(esk10_0,k2_relat_1(esk11_0))), inference(spm,[status(thm)],[c_0_55, c_0_49])).
% 1.83/2.05  cnf(c_0_60, negated_conjecture, (~r2_hidden(esk10_0,k3_relat_1(esk11_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_56, c_0_57])])).
% 1.83/2.05  cnf(c_0_61, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_60]), ['proof']).
% 1.83/2.05  # SZS output end CNFRefutation
% 1.83/2.05  # Proof object total steps             : 62
% 1.83/2.05  # Proof object clause steps            : 33
% 1.83/2.05  # Proof object formula steps           : 29
% 1.83/2.05  # Proof object conjectures             : 16
% 1.83/2.05  # Proof object clause conjectures      : 13
% 1.83/2.05  # Proof object formula conjectures     : 3
% 1.83/2.05  # Proof object initial clauses used    : 16
% 1.83/2.05  # Proof object initial formulas used   : 14
% 1.83/2.05  # Proof object generating inferences   : 10
% 1.83/2.05  # Proof object simplifying inferences  : 30
% 1.83/2.05  # Training examples: 0 positive, 0 negative
% 1.83/2.05  # Parsed axioms                        : 17
% 1.83/2.05  # Removed by relevancy pruning/SinE    : 0
% 1.83/2.05  # Initial clauses                      : 30
% 1.83/2.05  # Removed in clause preprocessing      : 7
% 1.83/2.05  # Initial clauses in saturation        : 23
% 1.83/2.05  # Processed clauses                    : 2092
% 1.83/2.05  # ...of these trivial                  : 10
% 1.83/2.05  # ...subsumed                          : 614
% 1.83/2.05  # ...remaining for further processing  : 1468
% 1.83/2.05  # Other redundant clauses eliminated   : 6
% 1.83/2.05  # Clauses deleted for lack of memory   : 0
% 1.83/2.05  # Backward-subsumed                    : 49
% 1.83/2.05  # Backward-rewritten                   : 19
% 1.83/2.05  # Generated clauses                    : 155497
% 1.83/2.05  # ...of the previous two non-trivial   : 154973
% 1.83/2.05  # Contextual simplify-reflections      : 7
% 1.83/2.05  # Paramodulations                      : 155481
% 1.83/2.05  # Factorizations                       : 10
% 1.83/2.05  # Equation resolutions                 : 6
% 1.83/2.05  # Propositional unsat checks           : 0
% 1.83/2.05  #    Propositional check models        : 0
% 1.83/2.05  #    Propositional check unsatisfiable : 0
% 1.83/2.05  #    Propositional clauses             : 0
% 1.83/2.05  #    Propositional clauses after purity: 0
% 1.83/2.05  #    Propositional unsat core size     : 0
% 1.83/2.05  #    Propositional preprocessing time  : 0.000
% 1.83/2.05  #    Propositional encoding time       : 0.000
% 1.83/2.05  #    Propositional solver time         : 0.000
% 1.83/2.05  #    Success case prop preproc time    : 0.000
% 1.83/2.05  #    Success case prop encoding time   : 0.000
% 1.83/2.05  #    Success case prop solver time     : 0.000
% 1.83/2.05  # Current number of processed clauses  : 1371
% 1.83/2.05  #    Positive orientable unit clauses  : 206
% 1.83/2.05  #    Positive unorientable unit clauses: 1
% 1.83/2.05  #    Negative unit clauses             : 1
% 1.83/2.05  #    Non-unit-clauses                  : 1163
% 1.83/2.05  # Current number of unprocessed clauses: 152868
% 1.83/2.05  # ...number of literals in the above   : 888565
% 1.83/2.05  # Current number of archived formulas  : 0
% 1.83/2.05  # Current number of archived clauses   : 98
% 1.83/2.05  # Clause-clause subsumption calls (NU) : 140852
% 1.83/2.05  # Rec. Clause-clause subsumption calls : 37219
% 1.83/2.05  # Non-unit clause-clause subsumptions  : 670
% 1.83/2.05  # Unit Clause-clause subsumption calls : 7956
% 1.83/2.05  # Rewrite failures with RHS unbound    : 0
% 1.83/2.05  # BW rewrite match attempts            : 1386
% 1.83/2.05  # BW rewrite match successes           : 5
% 1.83/2.05  # Condensation attempts                : 0
% 1.83/2.05  # Condensation successes               : 0
% 1.83/2.05  # Termbank termtop insertions          : 5478132
% 1.83/2.05  
% 1.83/2.05  # -------------------------------------------------
% 1.83/2.05  # User time                : 1.650 s
% 1.83/2.05  # System time              : 0.065 s
% 1.83/2.05  # Total time               : 1.715 s
% 1.83/2.05  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
