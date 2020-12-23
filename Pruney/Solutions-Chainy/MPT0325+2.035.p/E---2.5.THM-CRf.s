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
% DateTime   : Thu Dec  3 10:44:10 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 319 expanded)
%              Number of clauses        :   40 ( 152 expanded)
%              Number of leaves         :    9 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  160 ( 997 expanded)
%              Number of equality atoms :   47 ( 357 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t138_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
     => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
        | ( r1_tarski(X1,X3)
          & r1_tarski(X2,X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_9,plain,(
    ! [X13,X14,X16,X17,X18] :
      ( ( r1_xboole_0(X13,X14)
        | r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)) )
      & ( ~ r2_hidden(X18,k3_xboole_0(X16,X17))
        | ~ r1_xboole_0(X16,X17) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_10,plain,(
    ! [X20,X21] : k4_xboole_0(X20,k4_xboole_0(X20,X21)) = k3_xboole_0(X20,X21) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_13,plain,(
    ! [X19] : k4_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_14,plain,(
    ! [X22] : r1_xboole_0(X22,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_15,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_16,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X2)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_19,plain,(
    ! [X23,X24,X25,X26,X29,X30,X31,X32,X33,X34,X36,X37] :
      ( ( r2_hidden(esk3_4(X23,X24,X25,X26),X23)
        | ~ r2_hidden(X26,X25)
        | X25 != k2_zfmisc_1(X23,X24) )
      & ( r2_hidden(esk4_4(X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k2_zfmisc_1(X23,X24) )
      & ( X26 = k4_tarski(esk3_4(X23,X24,X25,X26),esk4_4(X23,X24,X25,X26))
        | ~ r2_hidden(X26,X25)
        | X25 != k2_zfmisc_1(X23,X24) )
      & ( ~ r2_hidden(X30,X23)
        | ~ r2_hidden(X31,X24)
        | X29 != k4_tarski(X30,X31)
        | r2_hidden(X29,X25)
        | X25 != k2_zfmisc_1(X23,X24) )
      & ( ~ r2_hidden(esk5_3(X32,X33,X34),X34)
        | ~ r2_hidden(X36,X32)
        | ~ r2_hidden(X37,X33)
        | esk5_3(X32,X33,X34) != k4_tarski(X36,X37)
        | X34 = k2_zfmisc_1(X32,X33) )
      & ( r2_hidden(esk6_3(X32,X33,X34),X32)
        | r2_hidden(esk5_3(X32,X33,X34),X34)
        | X34 = k2_zfmisc_1(X32,X33) )
      & ( r2_hidden(esk7_3(X32,X33,X34),X33)
        | r2_hidden(esk5_3(X32,X33,X34),X34)
        | X34 = k2_zfmisc_1(X32,X33) )
      & ( esk5_3(X32,X33,X34) = k4_tarski(esk6_3(X32,X33,X34),esk7_3(X32,X33,X34))
        | r2_hidden(esk5_3(X32,X33,X34),X34)
        | X34 = k2_zfmisc_1(X32,X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_20,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))
       => ( k2_zfmisc_1(X1,X2) = k1_xboole_0
          | ( r1_tarski(X1,X3)
            & r1_tarski(X2,X4) ) ) ) ),
    inference(assume_negation,[status(cth)],[t138_zfmisc_1])).

cnf(c_0_23,plain,
    ( X1 != k2_zfmisc_1(k1_xboole_0,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_25,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))
    & k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0
    & ( ~ r1_tarski(esk8_0,esk10_0)
      | ~ r1_tarski(esk9_0,esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).

cnf(c_0_26,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X40,X41,X42,X43] :
      ( ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( r2_hidden(X41,X43)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( ~ r2_hidden(X40,X42)
        | ~ r2_hidden(X41,X43)
        | r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_29,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X1 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)
    | r2_hidden(esk5_3(k2_zfmisc_1(k1_xboole_0,X2),X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_32,plain,(
    ! [X44,X45] :
      ( ( k2_zfmisc_1(X44,X45) != k1_xboole_0
        | X44 = k1_xboole_0
        | X45 = k1_xboole_0 )
      & ( X44 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 )
      & ( X45 != k1_xboole_0
        | k2_zfmisc_1(X44,X45) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))
    | ~ r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_20,c_0_31])).

cnf(c_0_36,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_40,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk9_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_35]),c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk11_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_40,c_0_36])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(X1,esk10_0)
    | ~ r2_hidden(esk1_2(X1,esk10_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,esk11_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_44]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk10_0)
    | ~ r1_tarski(esk9_0,esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_55,negated_conjecture,
    ( r1_tarski(esk8_0,esk10_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(X1,esk11_0)
    | ~ r2_hidden(esk1_2(X1,esk11_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( ~ r1_tarski(esk9_0,esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:39:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_B02_F1_AE_CS_SP_PS_S0Y
% 0.19/0.38  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.028 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.19/0.38  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.38  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 0.19/0.38  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.19/0.38  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.19/0.38  fof(t138_zfmisc_1, conjecture, ![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 0.19/0.38  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.38  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.19/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.19/0.38  fof(c_0_9, plain, ![X13, X14, X16, X17, X18]:((r1_xboole_0(X13,X14)|r2_hidden(esk2_2(X13,X14),k3_xboole_0(X13,X14)))&(~r2_hidden(X18,k3_xboole_0(X16,X17))|~r1_xboole_0(X16,X17))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.19/0.38  fof(c_0_10, plain, ![X20, X21]:k4_xboole_0(X20,k4_xboole_0(X20,X21))=k3_xboole_0(X20,X21), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.38  cnf(c_0_11, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.38  cnf(c_0_12, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.38  fof(c_0_13, plain, ![X19]:k4_xboole_0(X19,k1_xboole_0)=X19, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.19/0.38  fof(c_0_14, plain, ![X22]:r1_xboole_0(X22,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.19/0.38  cnf(c_0_15, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_11, c_0_12])).
% 0.19/0.38  cnf(c_0_16, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_17, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_18, plain, (~r2_hidden(X1,k4_xboole_0(X2,X2))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.19/0.38  fof(c_0_19, plain, ![X23, X24, X25, X26, X29, X30, X31, X32, X33, X34, X36, X37]:(((((r2_hidden(esk3_4(X23,X24,X25,X26),X23)|~r2_hidden(X26,X25)|X25!=k2_zfmisc_1(X23,X24))&(r2_hidden(esk4_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k2_zfmisc_1(X23,X24)))&(X26=k4_tarski(esk3_4(X23,X24,X25,X26),esk4_4(X23,X24,X25,X26))|~r2_hidden(X26,X25)|X25!=k2_zfmisc_1(X23,X24)))&(~r2_hidden(X30,X23)|~r2_hidden(X31,X24)|X29!=k4_tarski(X30,X31)|r2_hidden(X29,X25)|X25!=k2_zfmisc_1(X23,X24)))&((~r2_hidden(esk5_3(X32,X33,X34),X34)|(~r2_hidden(X36,X32)|~r2_hidden(X37,X33)|esk5_3(X32,X33,X34)!=k4_tarski(X36,X37))|X34=k2_zfmisc_1(X32,X33))&(((r2_hidden(esk6_3(X32,X33,X34),X32)|r2_hidden(esk5_3(X32,X33,X34),X34)|X34=k2_zfmisc_1(X32,X33))&(r2_hidden(esk7_3(X32,X33,X34),X33)|r2_hidden(esk5_3(X32,X33,X34),X34)|X34=k2_zfmisc_1(X32,X33)))&(esk5_3(X32,X33,X34)=k4_tarski(esk6_3(X32,X33,X34),esk7_3(X32,X33,X34))|r2_hidden(esk5_3(X32,X33,X34),X34)|X34=k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.19/0.38  cnf(c_0_20, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_18, c_0_16])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_22, negated_conjecture, ~(![X1, X2, X3, X4]:(r1_tarski(k2_zfmisc_1(X1,X2),k2_zfmisc_1(X3,X4))=>(k2_zfmisc_1(X1,X2)=k1_xboole_0|(r1_tarski(X1,X3)&r1_tarski(X2,X4))))), inference(assume_negation,[status(cth)],[t138_zfmisc_1])).
% 0.19/0.38  cnf(c_0_23, plain, (X1!=k2_zfmisc_1(k1_xboole_0,X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.38  fof(c_0_24, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.38  fof(c_0_25, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))&(k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0&(~r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_22])])])).
% 0.19/0.38  cnf(c_0_26, plain, (~r2_hidden(X1,k2_zfmisc_1(k1_xboole_0,X2))), inference(er,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_27, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_28, plain, ![X40, X41, X42, X43]:(((r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)))&(r2_hidden(X41,X43)|~r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43))))&(~r2_hidden(X40,X42)|~r2_hidden(X41,X43)|r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_29, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk8_0,esk9_0),k2_zfmisc_1(esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_31, plain, (X1=k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2),X3)|r2_hidden(esk5_3(k2_zfmisc_1(k1_xboole_0,X2),X3,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.19/0.38  fof(c_0_32, plain, ![X44, X45]:((k2_zfmisc_1(X44,X45)!=k1_xboole_0|(X44=k1_xboole_0|X45=k1_xboole_0))&((X44!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0)&(X45!=k1_xboole_0|k2_zfmisc_1(X44,X45)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.19/0.38  cnf(c_0_33, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))|~r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.38  cnf(c_0_35, plain, (k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)=k1_xboole_0), inference(spm,[status(thm)],[c_0_20, c_0_31])).
% 0.19/0.38  cnf(c_0_36, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.38  cnf(c_0_38, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_39, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_41, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.38  cnf(c_0_42, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_43, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X2,esk9_0)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.38  cnf(c_0_44, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_35]), c_0_39])).
% 0.19/0.38  cnf(c_0_45, negated_conjecture, (esk9_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk11_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.19/0.38  cnf(c_0_47, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (r2_hidden(X1,esk10_0)|~r2_hidden(X1,esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (r2_hidden(X1,esk11_0)|~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_46, c_0_38])).
% 0.19/0.38  cnf(c_0_50, negated_conjecture, (esk8_0!=k1_xboole_0), inference(spm,[status(thm)],[c_0_40, c_0_36])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r1_tarski(X1,esk10_0)|~r2_hidden(esk1_2(X1,esk10_0),esk8_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.19/0.38  cnf(c_0_52, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(X1,esk11_0)|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_44]), c_0_50])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (~r1_tarski(esk8_0,esk10_0)|~r1_tarski(esk9_0,esk11_0)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, (r1_tarski(esk8_0,esk10_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.38  cnf(c_0_56, negated_conjecture, (r1_tarski(X1,esk11_0)|~r2_hidden(esk1_2(X1,esk11_0),esk9_0)), inference(spm,[status(thm)],[c_0_47, c_0_53])).
% 0.19/0.38  cnf(c_0_57, negated_conjecture, (~r1_tarski(esk9_0,esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.19/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_52]), c_0_57]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 59
% 0.19/0.38  # Proof object clause steps            : 40
% 0.19/0.38  # Proof object formula steps           : 19
% 0.19/0.38  # Proof object conjectures             : 20
% 0.19/0.38  # Proof object clause conjectures      : 17
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 9
% 0.19/0.38  # Proof object generating inferences   : 20
% 0.19/0.38  # Proof object simplifying inferences  : 10
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 9
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 25
% 0.19/0.38  # Removed in clause preprocessing      : 1
% 0.19/0.38  # Initial clauses in saturation        : 24
% 0.19/0.38  # Processed clauses                    : 497
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 329
% 0.19/0.38  # ...remaining for further processing  : 168
% 0.19/0.38  # Other redundant clauses eliminated   : 1
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 7
% 0.19/0.38  # Backward-rewritten                   : 45
% 0.19/0.38  # Generated clauses                    : 926
% 0.19/0.38  # ...of the previous two non-trivial   : 787
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 900
% 0.19/0.38  # Factorizations                       : 0
% 0.19/0.38  # Equation resolutions                 : 26
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
% 0.19/0.38  # Current number of processed clauses  : 92
% 0.19/0.38  #    Positive orientable unit clauses  : 9
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 6
% 0.19/0.38  #    Non-unit-clauses                  : 77
% 0.19/0.38  # Current number of unprocessed clauses: 265
% 0.19/0.38  # ...number of literals in the above   : 805
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 77
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 1089
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 780
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 158
% 0.19/0.38  # Unit Clause-clause subsumption calls : 147
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 47
% 0.19/0.38  # BW rewrite match successes           : 15
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 8349
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.043 s
% 0.19/0.38  # System time              : 0.005 s
% 0.19/0.38  # Total time               : 0.049 s
% 0.19/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
