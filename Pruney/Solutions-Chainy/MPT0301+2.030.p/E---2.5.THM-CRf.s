%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:28 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   55 (1615 expanded)
%              Number of clauses        :   34 ( 743 expanded)
%              Number of leaves         :   10 ( 421 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 (3558 expanded)
%              Number of equality atoms :   54 (1548 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t113_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t79_xboole_1,axiom,(
    ! [X1,X2] : r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(t100_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(t5_boole,axiom,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k1_xboole_0
      <=> ( X1 = k1_xboole_0
          | X2 = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t113_zfmisc_1])).

fof(c_0_11,plain,(
    ! [X21,X22] : r1_xboole_0(k4_xboole_0(X21,X22),X22) ),
    inference(variable_rename,[status(thm)],[t79_xboole_1])).

fof(c_0_12,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(X15,k3_xboole_0(X15,X16)) ),
    inference(variable_rename,[status(thm)],[t100_xboole_1])).

fof(c_0_13,plain,(
    ! [X19] :
      ( ~ r1_tarski(X19,k1_xboole_0)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

fof(c_0_14,plain,(
    ! [X17,X18] : r1_tarski(k3_xboole_0(X17,X18),X17) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_15,negated_conjecture,
    ( ( esk8_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( esk9_0 != k1_xboole_0
      | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 )
    & ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
      | esk8_0 = k1_xboole_0
      | esk9_0 = k1_xboole_0 ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).

fof(c_0_16,plain,(
    ! [X13] :
      ( X13 = k1_xboole_0
      | r2_hidden(esk2_1(X13),X13) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(k4_xboole_0(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_21,plain,(
    ! [X20] : k5_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(variable_rename,[status(thm)],[t5_boole])).

fof(c_0_22,plain,(
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

cnf(c_0_23,negated_conjecture,
    ( esk8_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_25,plain,(
    ! [X7,X8,X10,X11,X12] :
      ( ( r1_xboole_0(X7,X8)
        | r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)) )
      & ( ~ r2_hidden(X12,k3_xboole_0(X10,X11))
        | ~ r1_xboole_0(X10,X11) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

cnf(c_0_26,plain,
    ( r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2) ),
    inference(rw,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_27,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_28,plain,
    ( k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_0),esk8_0)
    | k2_zfmisc_1(k1_xboole_0,esk9_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( esk9_0 != k1_xboole_0
    | k2_zfmisc_1(esk8_0,esk9_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_34,plain,(
    ! [X40,X41,X42,X43] :
      ( ( r2_hidden(X40,X42)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( r2_hidden(X41,X43)
        | ~ r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) )
      & ( ~ r2_hidden(X40,X42)
        | ~ r2_hidden(X41,X43)
        | r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk2_1(k2_zfmisc_1(k1_xboole_0,esk9_0)),k2_zfmisc_1(k1_xboole_0,esk9_0))
    | r2_hidden(esk2_1(esk8_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_30,c_0_24])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk2_1(esk9_0),esk9_0)
    | k2_zfmisc_1(esk8_0,k1_xboole_0) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_40,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_1(esk8_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_1(k2_zfmisc_1(esk8_0,k1_xboole_0)),k2_zfmisc_1(esk8_0,k1_xboole_0))
    | r2_hidden(esk2_1(esk9_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_24])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk8_0),X1),k2_zfmisc_1(esk8_0,X2))
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk2_1(esk9_0),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_37])).

cnf(c_0_46,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_37,c_0_24])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk8_0),esk2_1(esk8_0)),k2_zfmisc_1(esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_1(esk8_0),esk2_1(esk9_0)),k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_49,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k1_xboole_0
    | esk8_0 = k1_xboole_0
    | esk9_0 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk2_1(k2_zfmisc_1(esk8_0,esk8_0)),k2_zfmisc_1(esk8_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( esk9_0 = k1_xboole_0
    | esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_37])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(esk3_4(esk8_0,esk8_0,k2_zfmisc_1(esk8_0,esk8_0),esk2_1(k2_zfmisc_1(esk8_0,esk8_0))),esk8_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_51]),c_0_37])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_53]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.37  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.13/0.37  # and selection function SelectNegativeLiterals.
% 0.13/0.37  #
% 0.13/0.37  # Preprocessing time       : 0.027 s
% 0.13/0.37  # Presaturation interreduction done
% 0.13/0.37  
% 0.13/0.37  # Proof found!
% 0.13/0.37  # SZS status Theorem
% 0.13/0.37  # SZS output start CNFRefutation
% 0.13/0.37  fof(t113_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.37  fof(t79_xboole_1, axiom, ![X1, X2]:r1_xboole_0(k4_xboole_0(X1,X2),X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 0.13/0.37  fof(t100_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 0.13/0.37  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.13/0.37  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 0.13/0.37  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.13/0.37  fof(t5_boole, axiom, ![X1]:k5_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 0.13/0.37  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.13/0.37  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.13/0.37  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.13/0.37  fof(c_0_10, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0))), inference(assume_negation,[status(cth)],[t113_zfmisc_1])).
% 0.13/0.37  fof(c_0_11, plain, ![X21, X22]:r1_xboole_0(k4_xboole_0(X21,X22),X22), inference(variable_rename,[status(thm)],[t79_xboole_1])).
% 0.13/0.37  fof(c_0_12, plain, ![X15, X16]:k4_xboole_0(X15,X16)=k5_xboole_0(X15,k3_xboole_0(X15,X16)), inference(variable_rename,[status(thm)],[t100_xboole_1])).
% 0.13/0.37  fof(c_0_13, plain, ![X19]:(~r1_tarski(X19,k1_xboole_0)|X19=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.13/0.37  fof(c_0_14, plain, ![X17, X18]:r1_tarski(k3_xboole_0(X17,X18),X17), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 0.13/0.37  fof(c_0_15, negated_conjecture, (((esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0)&(esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0))&(k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|(esk8_0=k1_xboole_0|esk9_0=k1_xboole_0))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])])).
% 0.13/0.37  fof(c_0_16, plain, ![X13]:(X13=k1_xboole_0|r2_hidden(esk2_1(X13),X13)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.13/0.37  cnf(c_0_17, plain, (r1_xboole_0(k4_xboole_0(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.37  cnf(c_0_18, plain, (k4_xboole_0(X1,X2)=k5_xboole_0(X1,k3_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.37  cnf(c_0_19, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.37  cnf(c_0_20, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.37  fof(c_0_21, plain, ![X20]:k5_xboole_0(X20,k1_xboole_0)=X20, inference(variable_rename,[status(thm)],[t5_boole])).
% 0.13/0.37  fof(c_0_22, plain, ![X23, X24, X25, X26, X29, X30, X31, X32, X33, X34, X36, X37]:(((((r2_hidden(esk3_4(X23,X24,X25,X26),X23)|~r2_hidden(X26,X25)|X25!=k2_zfmisc_1(X23,X24))&(r2_hidden(esk4_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k2_zfmisc_1(X23,X24)))&(X26=k4_tarski(esk3_4(X23,X24,X25,X26),esk4_4(X23,X24,X25,X26))|~r2_hidden(X26,X25)|X25!=k2_zfmisc_1(X23,X24)))&(~r2_hidden(X30,X23)|~r2_hidden(X31,X24)|X29!=k4_tarski(X30,X31)|r2_hidden(X29,X25)|X25!=k2_zfmisc_1(X23,X24)))&((~r2_hidden(esk5_3(X32,X33,X34),X34)|(~r2_hidden(X36,X32)|~r2_hidden(X37,X33)|esk5_3(X32,X33,X34)!=k4_tarski(X36,X37))|X34=k2_zfmisc_1(X32,X33))&(((r2_hidden(esk6_3(X32,X33,X34),X32)|r2_hidden(esk5_3(X32,X33,X34),X34)|X34=k2_zfmisc_1(X32,X33))&(r2_hidden(esk7_3(X32,X33,X34),X33)|r2_hidden(esk5_3(X32,X33,X34),X34)|X34=k2_zfmisc_1(X32,X33)))&(esk5_3(X32,X33,X34)=k4_tarski(esk6_3(X32,X33,X34),esk7_3(X32,X33,X34))|r2_hidden(esk5_3(X32,X33,X34),X34)|X34=k2_zfmisc_1(X32,X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.13/0.37  cnf(c_0_23, negated_conjecture, (esk8_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.37  fof(c_0_25, plain, ![X7, X8, X10, X11, X12]:((r1_xboole_0(X7,X8)|r2_hidden(esk1_2(X7,X8),k3_xboole_0(X7,X8)))&(~r2_hidden(X12,k3_xboole_0(X10,X11))|~r1_xboole_0(X10,X11))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.13/0.37  cnf(c_0_26, plain, (r1_xboole_0(k5_xboole_0(X1,k3_xboole_0(X1,X2)),X2)), inference(rw,[status(thm)],[c_0_17, c_0_18])).
% 0.13/0.37  cnf(c_0_27, plain, (k3_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.37  cnf(c_0_28, plain, (k5_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.37  cnf(c_0_29, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_30, negated_conjecture, (r2_hidden(esk2_1(esk8_0),esk8_0)|k2_zfmisc_1(k1_xboole_0,esk9_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.13/0.37  cnf(c_0_31, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.13/0.37  cnf(c_0_32, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.13/0.37  cnf(c_0_33, negated_conjecture, (esk9_0!=k1_xboole_0|k2_zfmisc_1(esk8_0,esk9_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  fof(c_0_34, plain, ![X40, X41, X42, X43]:(((r2_hidden(X40,X42)|~r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)))&(r2_hidden(X41,X43)|~r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43))))&(~r2_hidden(X40,X42)|~r2_hidden(X41,X43)|r2_hidden(k4_tarski(X40,X41),k2_zfmisc_1(X42,X43)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.13/0.37  cnf(c_0_35, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_29])).
% 0.13/0.37  cnf(c_0_36, negated_conjecture, (r2_hidden(esk2_1(k2_zfmisc_1(k1_xboole_0,esk9_0)),k2_zfmisc_1(k1_xboole_0,esk9_0))|r2_hidden(esk2_1(esk8_0),esk8_0)), inference(spm,[status(thm)],[c_0_30, c_0_24])).
% 0.13/0.37  cnf(c_0_37, plain, (~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_27])).
% 0.13/0.37  cnf(c_0_38, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.37  cnf(c_0_39, negated_conjecture, (r2_hidden(esk2_1(esk9_0),esk9_0)|k2_zfmisc_1(esk8_0,k1_xboole_0)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 0.13/0.37  cnf(c_0_40, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.13/0.37  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_1(esk8_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.13/0.37  cnf(c_0_42, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.37  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_1(k2_zfmisc_1(esk8_0,k1_xboole_0)),k2_zfmisc_1(esk8_0,k1_xboole_0))|r2_hidden(esk2_1(esk9_0),esk9_0)), inference(spm,[status(thm)],[c_0_39, c_0_24])).
% 0.13/0.37  cnf(c_0_44, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk8_0),X1),k2_zfmisc_1(esk8_0,X2))|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.37  cnf(c_0_45, negated_conjecture, (r2_hidden(esk2_1(esk9_0),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_37])).
% 0.13/0.37  cnf(c_0_46, plain, (r2_hidden(esk2_1(X1),X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_37, c_0_24])).
% 0.13/0.37  cnf(c_0_47, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk8_0),esk2_1(esk8_0)),k2_zfmisc_1(esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_44, c_0_41])).
% 0.13/0.37  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(esk2_1(esk8_0),esk2_1(esk9_0)),k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.13/0.37  cnf(c_0_49, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k1_xboole_0|esk8_0=k1_xboole_0|esk9_0=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.37  cnf(c_0_50, negated_conjecture, (r2_hidden(esk2_1(k2_zfmisc_1(esk8_0,esk8_0)),k2_zfmisc_1(esk8_0,esk8_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.13/0.37  cnf(c_0_51, negated_conjecture, (esk9_0=k1_xboole_0|esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_49]), c_0_37])).
% 0.13/0.37  cnf(c_0_52, negated_conjecture, (r2_hidden(esk3_4(esk8_0,esk8_0,k2_zfmisc_1(esk8_0,esk8_0),esk2_1(k2_zfmisc_1(esk8_0,esk8_0))),esk8_0)), inference(spm,[status(thm)],[c_0_35, c_0_50])).
% 0.13/0.37  cnf(c_0_53, negated_conjecture, (esk8_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_51]), c_0_37])).
% 0.13/0.37  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_53]), c_0_37]), ['proof']).
% 0.13/0.37  # SZS output end CNFRefutation
% 0.13/0.37  # Proof object total steps             : 55
% 0.13/0.37  # Proof object clause steps            : 34
% 0.13/0.37  # Proof object formula steps           : 21
% 0.13/0.37  # Proof object conjectures             : 20
% 0.13/0.37  # Proof object clause conjectures      : 17
% 0.13/0.37  # Proof object formula conjectures     : 3
% 0.13/0.37  # Proof object initial clauses used    : 13
% 0.13/0.37  # Proof object initial formulas used   : 10
% 0.13/0.37  # Proof object generating inferences   : 17
% 0.13/0.37  # Proof object simplifying inferences  : 17
% 0.13/0.37  # Training examples: 0 positive, 0 negative
% 0.13/0.37  # Parsed axioms                        : 10
% 0.13/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.37  # Initial clauses                      : 22
% 0.13/0.37  # Removed in clause preprocessing      : 1
% 0.13/0.37  # Initial clauses in saturation        : 21
% 0.13/0.37  # Processed clauses                    : 95
% 0.13/0.37  # ...of these trivial                  : 2
% 0.13/0.37  # ...subsumed                          : 23
% 0.13/0.37  # ...remaining for further processing  : 70
% 0.13/0.37  # Other redundant clauses eliminated   : 7
% 0.13/0.37  # Clauses deleted for lack of memory   : 0
% 0.13/0.37  # Backward-subsumed                    : 1
% 0.13/0.37  # Backward-rewritten                   : 21
% 0.13/0.37  # Generated clauses                    : 236
% 0.13/0.37  # ...of the previous two non-trivial   : 178
% 0.13/0.37  # Contextual simplify-reflections      : 0
% 0.13/0.37  # Paramodulations                      : 230
% 0.13/0.37  # Factorizations                       : 0
% 0.13/0.37  # Equation resolutions                 : 7
% 0.13/0.37  # Propositional unsat checks           : 0
% 0.13/0.37  #    Propositional check models        : 0
% 0.13/0.37  #    Propositional check unsatisfiable : 0
% 0.13/0.37  #    Propositional clauses             : 0
% 0.13/0.37  #    Propositional clauses after purity: 0
% 0.13/0.37  #    Propositional unsat core size     : 0
% 0.13/0.37  #    Propositional preprocessing time  : 0.000
% 0.13/0.37  #    Propositional encoding time       : 0.000
% 0.13/0.37  #    Propositional solver time         : 0.000
% 0.13/0.37  #    Success case prop preproc time    : 0.000
% 0.13/0.37  #    Success case prop encoding time   : 0.000
% 0.13/0.37  #    Success case prop solver time     : 0.000
% 0.13/0.37  # Current number of processed clauses  : 24
% 0.13/0.37  #    Positive orientable unit clauses  : 8
% 0.13/0.37  #    Positive unorientable unit clauses: 0
% 0.13/0.37  #    Negative unit clauses             : 2
% 0.13/0.37  #    Non-unit-clauses                  : 14
% 0.13/0.37  # Current number of unprocessed clauses: 123
% 0.13/0.37  # ...number of literals in the above   : 265
% 0.13/0.37  # Current number of archived formulas  : 0
% 0.13/0.37  # Current number of archived clauses   : 43
% 0.13/0.37  # Clause-clause subsumption calls (NU) : 92
% 0.13/0.37  # Rec. Clause-clause subsumption calls : 73
% 0.13/0.37  # Non-unit clause-clause subsumptions  : 16
% 0.13/0.37  # Unit Clause-clause subsumption calls : 10
% 0.13/0.37  # Rewrite failures with RHS unbound    : 0
% 0.13/0.37  # BW rewrite match attempts            : 3
% 0.13/0.37  # BW rewrite match successes           : 3
% 0.13/0.37  # Condensation attempts                : 0
% 0.13/0.37  # Condensation successes               : 0
% 0.13/0.37  # Termbank termtop insertions          : 4283
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.029 s
% 0.13/0.37  # System time              : 0.006 s
% 0.13/0.37  # Total time               : 0.035 s
% 0.13/0.37  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
