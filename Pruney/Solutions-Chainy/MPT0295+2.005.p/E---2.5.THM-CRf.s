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
% DateTime   : Thu Dec  3 10:43:22 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  77 expanded)
%              Number of clauses        :   31 (  38 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  153 ( 352 expanded)
%              Number of equality atoms :   40 ( 109 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(t103_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

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

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_6,plain,(
    ! [X20,X21,X22,X23,X24,X25] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X20
        | X21 != k1_tarski(X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k1_tarski(X20) )
      & ( ~ r2_hidden(esk3_2(X24,X25),X25)
        | esk3_2(X24,X25) != X24
        | X25 = k1_tarski(X24) )
      & ( r2_hidden(esk3_2(X24,X25),X25)
        | esk3_2(X24,X25) = X24
        | X25 = k1_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X4,X1)
          & ! [X5,X6] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & X4 = k4_tarski(X5,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t103_zfmisc_1])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X11,X12,X14,X15,X16] :
      ( ( r2_hidden(esk2_2(X11,X12),X11)
        | r1_xboole_0(X11,X12) )
      & ( r2_hidden(esk2_2(X11,X12),X12)
        | r1_xboole_0(X11,X12) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | ~ r1_xboole_0(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_10,plain,(
    ! [X27,X28,X29,X30,X33,X34,X35,X36,X37,X38,X40,X41] :
      ( ( r2_hidden(esk4_4(X27,X28,X29,X30),X27)
        | ~ r2_hidden(X30,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( r2_hidden(esk5_4(X27,X28,X29,X30),X28)
        | ~ r2_hidden(X30,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( X30 = k4_tarski(esk4_4(X27,X28,X29,X30),esk5_4(X27,X28,X29,X30))
        | ~ r2_hidden(X30,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( ~ r2_hidden(X34,X27)
        | ~ r2_hidden(X35,X28)
        | X33 != k4_tarski(X34,X35)
        | r2_hidden(X33,X29)
        | X29 != k2_zfmisc_1(X27,X28) )
      & ( ~ r2_hidden(esk6_3(X36,X37,X38),X38)
        | ~ r2_hidden(X40,X36)
        | ~ r2_hidden(X41,X37)
        | esk6_3(X36,X37,X38) != k4_tarski(X40,X41)
        | X38 = k2_zfmisc_1(X36,X37) )
      & ( r2_hidden(esk7_3(X36,X37,X38),X36)
        | r2_hidden(esk6_3(X36,X37,X38),X38)
        | X38 = k2_zfmisc_1(X36,X37) )
      & ( r2_hidden(esk8_3(X36,X37,X38),X37)
        | r2_hidden(esk6_3(X36,X37,X38),X38)
        | X38 = k2_zfmisc_1(X36,X37) )
      & ( esk6_3(X36,X37,X38) = k4_tarski(esk7_3(X36,X37,X38),esk8_3(X36,X37,X38))
        | r2_hidden(esk6_3(X36,X37,X38),X38)
        | X38 = k2_zfmisc_1(X36,X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_11,plain,(
    ! [X17,X18,X19] :
      ( ~ r1_tarski(X17,X18)
      | ~ r1_xboole_0(X18,X19)
      | r1_xboole_0(X17,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_12,negated_conjecture,(
    ! [X48,X49] :
      ( r1_tarski(esk9_0,k2_zfmisc_1(esk10_0,esk11_0))
      & r2_hidden(esk12_0,esk9_0)
      & ( ~ r2_hidden(X48,esk10_0)
        | ~ r2_hidden(X49,esk11_0)
        | esk12_0 != k4_tarski(X48,X49) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( X1 = k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk9_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( esk2_2(X1,k1_tarski(X2)) = X2
    | r1_xboole_0(X1,k1_tarski(X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_20,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,esk10_0)
    | ~ r2_hidden(X2,esk11_0)
    | esk12_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,plain,
    ( k4_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( r2_hidden(esk5_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,negated_conjecture,
    ( r1_xboole_0(esk9_0,X1)
    | ~ r1_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_26,plain,
    ( r1_xboole_0(X1,k1_tarski(X2))
    | r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk12_0),esk11_0)
    | ~ r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk12_0),esk10_0)
    | ~ r2_hidden(esk12_0,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_33,negated_conjecture,
    ( r1_xboole_0(esk9_0,k1_tarski(X1))
    | r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( ~ r2_hidden(esk4_4(X1,esk11_0,k2_zfmisc_1(X1,esk11_0),esk12_0),esk10_0)
    | ~ r2_hidden(esk12_0,k2_zfmisc_1(X1,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))
    | ~ r2_hidden(X2,k1_tarski(X1))
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,plain,
    ( esk1_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_34]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(esk12_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_34]),c_0_39]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk12_0,esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:55:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.028 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 0.21/0.39  fof(t103_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 0.21/0.39  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.21/0.39  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.21/0.39  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.21/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.21/0.39  fof(c_0_6, plain, ![X20, X21, X22, X23, X24, X25]:(((~r2_hidden(X22,X21)|X22=X20|X21!=k1_tarski(X20))&(X23!=X20|r2_hidden(X23,X21)|X21!=k1_tarski(X20)))&((~r2_hidden(esk3_2(X24,X25),X25)|esk3_2(X24,X25)!=X24|X25=k1_tarski(X24))&(r2_hidden(esk3_2(X24,X25),X25)|esk3_2(X24,X25)=X24|X25=k1_tarski(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.21/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6)))))), inference(assume_negation,[status(cth)],[t103_zfmisc_1])).
% 0.21/0.39  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  fof(c_0_9, plain, ![X11, X12, X14, X15, X16]:(((r2_hidden(esk2_2(X11,X12),X11)|r1_xboole_0(X11,X12))&(r2_hidden(esk2_2(X11,X12),X12)|r1_xboole_0(X11,X12)))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|~r1_xboole_0(X14,X15))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.21/0.39  fof(c_0_10, plain, ![X27, X28, X29, X30, X33, X34, X35, X36, X37, X38, X40, X41]:(((((r2_hidden(esk4_4(X27,X28,X29,X30),X27)|~r2_hidden(X30,X29)|X29!=k2_zfmisc_1(X27,X28))&(r2_hidden(esk5_4(X27,X28,X29,X30),X28)|~r2_hidden(X30,X29)|X29!=k2_zfmisc_1(X27,X28)))&(X30=k4_tarski(esk4_4(X27,X28,X29,X30),esk5_4(X27,X28,X29,X30))|~r2_hidden(X30,X29)|X29!=k2_zfmisc_1(X27,X28)))&(~r2_hidden(X34,X27)|~r2_hidden(X35,X28)|X33!=k4_tarski(X34,X35)|r2_hidden(X33,X29)|X29!=k2_zfmisc_1(X27,X28)))&((~r2_hidden(esk6_3(X36,X37,X38),X38)|(~r2_hidden(X40,X36)|~r2_hidden(X41,X37)|esk6_3(X36,X37,X38)!=k4_tarski(X40,X41))|X38=k2_zfmisc_1(X36,X37))&(((r2_hidden(esk7_3(X36,X37,X38),X36)|r2_hidden(esk6_3(X36,X37,X38),X38)|X38=k2_zfmisc_1(X36,X37))&(r2_hidden(esk8_3(X36,X37,X38),X37)|r2_hidden(esk6_3(X36,X37,X38),X38)|X38=k2_zfmisc_1(X36,X37)))&(esk6_3(X36,X37,X38)=k4_tarski(esk7_3(X36,X37,X38),esk8_3(X36,X37,X38))|r2_hidden(esk6_3(X36,X37,X38),X38)|X38=k2_zfmisc_1(X36,X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.21/0.39  fof(c_0_11, plain, ![X17, X18, X19]:(~r1_tarski(X17,X18)|~r1_xboole_0(X18,X19)|r1_xboole_0(X17,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.21/0.39  fof(c_0_12, negated_conjecture, ![X48, X49]:((r1_tarski(esk9_0,k2_zfmisc_1(esk10_0,esk11_0))&r2_hidden(esk12_0,esk9_0))&(~r2_hidden(X48,esk10_0)|~r2_hidden(X49,esk11_0)|esk12_0!=k4_tarski(X48,X49))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])).
% 0.21/0.39  cnf(c_0_13, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_14, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_15, plain, (X1=k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_16, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_17, negated_conjecture, (r1_tarski(esk9_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_18, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_19, plain, (esk2_2(X1,k1_tarski(X2))=X2|r1_xboole_0(X1,k1_tarski(X2))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.21/0.39  fof(c_0_20, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.21/0.39  cnf(c_0_21, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,esk10_0)|~r2_hidden(X2,esk11_0)|esk12_0!=k4_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_23, plain, (k4_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.21/0.39  cnf(c_0_24, plain, (r2_hidden(esk5_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (r1_xboole_0(esk9_0,X1)|~r1_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.21/0.39  cnf(c_0_26, plain, (r1_xboole_0(X1,k1_tarski(X2))|r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.39  cnf(c_0_27, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_28, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_21])])).
% 0.21/0.39  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk12_0),esk11_0)|~r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk12_0),esk10_0)|~r2_hidden(esk12_0,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23])])).
% 0.21/0.39  cnf(c_0_30, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.21/0.39  cnf(c_0_31, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.21/0.39  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (r1_xboole_0(esk9_0,k1_tarski(X1))|r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.21/0.39  cnf(c_0_34, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.21/0.39  cnf(c_0_35, plain, (~v1_xboole_0(k1_tarski(X1))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.21/0.39  cnf(c_0_36, negated_conjecture, (~r2_hidden(esk4_4(X1,esk11_0,k2_zfmisc_1(X1,esk11_0),esk12_0),esk10_0)|~r2_hidden(esk12_0,k2_zfmisc_1(X1,esk11_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.39  cnf(c_0_37, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))|~r2_hidden(X2,k1_tarski(X1))|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.21/0.39  cnf(c_0_39, plain, (esk1_1(k1_tarski(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_34]), c_0_35])).
% 0.21/0.39  cnf(c_0_40, negated_conjecture, (~r2_hidden(esk12_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.21/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk10_0,esk11_0))|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_34]), c_0_39]), c_0_35])).
% 0.21/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk12_0,esk9_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.21/0.39  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 44
% 0.21/0.39  # Proof object clause steps            : 31
% 0.21/0.39  # Proof object formula steps           : 13
% 0.21/0.39  # Proof object conjectures             : 14
% 0.21/0.39  # Proof object clause conjectures      : 11
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 14
% 0.21/0.39  # Proof object initial formulas used   : 6
% 0.21/0.39  # Proof object generating inferences   : 12
% 0.21/0.39  # Proof object simplifying inferences  : 12
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 6
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 21
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 21
% 0.21/0.39  # Processed clauses                    : 241
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 86
% 0.21/0.39  # ...remaining for further processing  : 155
% 0.21/0.39  # Other redundant clauses eliminated   : 12
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 0
% 0.21/0.39  # Generated clauses                    : 946
% 0.21/0.39  # ...of the previous two non-trivial   : 926
% 0.21/0.39  # Contextual simplify-reflections      : 0
% 0.21/0.39  # Paramodulations                      : 934
% 0.21/0.39  # Factorizations                       : 2
% 0.21/0.39  # Equation resolutions                 : 12
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 128
% 0.21/0.39  #    Positive orientable unit clauses  : 4
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 3
% 0.21/0.39  #    Non-unit-clauses                  : 121
% 0.21/0.39  # Current number of unprocessed clauses: 727
% 0.21/0.39  # ...number of literals in the above   : 2135
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 21
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 3425
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 2552
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 86
% 0.21/0.39  # Unit Clause-clause subsumption calls : 58
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 1
% 0.21/0.39  # BW rewrite match successes           : 0
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 14566
% 0.21/0.40  
% 0.21/0.40  # -------------------------------------------------
% 0.21/0.40  # User time                : 0.046 s
% 0.21/0.40  # System time              : 0.006 s
% 0.21/0.40  # Total time               : 0.052 s
% 0.21/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
