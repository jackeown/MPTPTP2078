%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:23 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  58 expanded)
%              Number of clauses        :   27 (  28 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    9
%              Number of atoms          :  150 ( 312 expanded)
%              Number of equality atoms :   32 (  76 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(t103_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
        & r2_hidden(X4,X1)
        & ! [X5,X6] :
            ~ ( r2_hidden(X5,X2)
              & r2_hidden(X6,X3)
              & X4 = k4_tarski(X5,X6) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

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

fof(c_0_5,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( r2_hidden(X10,X7)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k4_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k4_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k4_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r1_tarski(X1,k2_zfmisc_1(X2,X3))
          & r2_hidden(X4,X1)
          & ! [X5,X6] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X6,X3)
                & X4 = k4_tarski(X5,X6) ) ) ),
    inference(assume_negation,[status(cth)],[t103_zfmisc_1])).

cnf(c_0_7,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_8,plain,(
    ! [X16,X17,X19,X20,X21] :
      ( ( r2_hidden(esk2_2(X16,X17),X16)
        | r1_xboole_0(X16,X17) )
      & ( r2_hidden(esk2_2(X16,X17),X17)
        | r1_xboole_0(X16,X17) )
      & ( ~ r2_hidden(X21,X19)
        | ~ r2_hidden(X21,X20)
        | ~ r1_xboole_0(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X22,X23,X24] :
      ( ~ r1_tarski(X22,X23)
      | ~ r1_xboole_0(X23,X24)
      | r1_xboole_0(X22,X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_10,negated_conjecture,(
    ! [X46,X47] :
      ( r1_tarski(esk8_0,k2_zfmisc_1(esk9_0,esk10_0))
      & r2_hidden(esk11_0,esk8_0)
      & ( ~ r2_hidden(X46,esk9_0)
        | ~ r2_hidden(X47,esk10_0)
        | esk11_0 != k4_tarski(X46,X47) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

cnf(c_0_11,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X25,X26,X27,X28,X31,X32,X33,X34,X35,X36,X38,X39] :
      ( ( r2_hidden(esk3_4(X25,X26,X27,X28),X25)
        | ~ r2_hidden(X28,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( r2_hidden(esk4_4(X25,X26,X27,X28),X26)
        | ~ r2_hidden(X28,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( X28 = k4_tarski(esk3_4(X25,X26,X27,X28),esk4_4(X25,X26,X27,X28))
        | ~ r2_hidden(X28,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( ~ r2_hidden(X32,X25)
        | ~ r2_hidden(X33,X26)
        | X31 != k4_tarski(X32,X33)
        | r2_hidden(X31,X27)
        | X27 != k2_zfmisc_1(X25,X26) )
      & ( ~ r2_hidden(esk5_3(X34,X35,X36),X36)
        | ~ r2_hidden(X38,X34)
        | ~ r2_hidden(X39,X35)
        | esk5_3(X34,X35,X36) != k4_tarski(X38,X39)
        | X36 = k2_zfmisc_1(X34,X35) )
      & ( r2_hidden(esk6_3(X34,X35,X36),X34)
        | r2_hidden(esk5_3(X34,X35,X36),X36)
        | X36 = k2_zfmisc_1(X34,X35) )
      & ( r2_hidden(esk7_3(X34,X35,X36),X35)
        | r2_hidden(esk5_3(X34,X35,X36),X36)
        | X36 = k2_zfmisc_1(X34,X35) )
      & ( esk5_3(X34,X35,X36) = k4_tarski(esk6_3(X34,X35,X36),esk7_3(X34,X35,X36))
        | r2_hidden(esk5_3(X34,X35,X36),X36)
        | X36 = k2_zfmisc_1(X34,X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

cnf(c_0_14,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(esk8_0,k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,plain,
    ( X1 = k4_tarski(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( r1_xboole_0(esk8_0,X1)
    | ~ r1_xboole_0(k2_zfmisc_1(esk9_0,esk10_0),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X2,esk10_0)
    | esk11_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,plain,
    ( k4_tarski(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_26,negated_conjecture,
    ( r1_xboole_0(esk8_0,k4_xboole_0(X1,k2_zfmisc_1(esk9_0,esk10_0))) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk11_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk10_0)
    | ~ r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23])])).

cnf(c_0_30,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,k2_zfmisc_1(esk9_0,esk10_0)))
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk11_0,k4_xboole_0(esk8_0,X1))
    | r2_hidden(esk11_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( ~ r2_hidden(esk3_4(X1,esk10_0,k2_zfmisc_1(X1,esk10_0),esk11_0),esk9_0)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(esk11_0,k2_zfmisc_1(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_28])])).

cnf(c_0_37,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:36:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.40  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.40  #
% 0.20/0.40  # Preprocessing time       : 0.024 s
% 0.20/0.40  # Presaturation interreduction done
% 0.20/0.40  
% 0.20/0.40  # Proof found!
% 0.20/0.40  # SZS status Theorem
% 0.20/0.40  # SZS output start CNFRefutation
% 0.20/0.40  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.20/0.40  fof(t103_zfmisc_1, conjecture, ![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 0.20/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.40  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.20/0.40  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.20/0.40  fof(c_0_5, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:((((r2_hidden(X10,X7)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|X9!=k4_xboole_0(X7,X8)))&(~r2_hidden(X11,X7)|r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k4_xboole_0(X7,X8)))&((~r2_hidden(esk1_3(X12,X13,X14),X14)|(~r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k4_xboole_0(X12,X13))&((r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k4_xboole_0(X12,X13))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.20/0.40  fof(c_0_6, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r1_tarski(X1,k2_zfmisc_1(X2,X3))&r2_hidden(X4,X1))&![X5, X6]:~(((r2_hidden(X5,X2)&r2_hidden(X6,X3))&X4=k4_tarski(X5,X6)))))), inference(assume_negation,[status(cth)],[t103_zfmisc_1])).
% 0.20/0.40  cnf(c_0_7, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.40  fof(c_0_8, plain, ![X16, X17, X19, X20, X21]:(((r2_hidden(esk2_2(X16,X17),X16)|r1_xboole_0(X16,X17))&(r2_hidden(esk2_2(X16,X17),X17)|r1_xboole_0(X16,X17)))&(~r2_hidden(X21,X19)|~r2_hidden(X21,X20)|~r1_xboole_0(X19,X20))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.40  fof(c_0_9, plain, ![X22, X23, X24]:(~r1_tarski(X22,X23)|~r1_xboole_0(X23,X24)|r1_xboole_0(X22,X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.20/0.40  fof(c_0_10, negated_conjecture, ![X46, X47]:((r1_tarski(esk8_0,k2_zfmisc_1(esk9_0,esk10_0))&r2_hidden(esk11_0,esk8_0))&(~r2_hidden(X46,esk9_0)|~r2_hidden(X47,esk10_0)|esk11_0!=k4_tarski(X46,X47))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.20/0.40  cnf(c_0_11, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_7])).
% 0.20/0.40  cnf(c_0_12, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  fof(c_0_13, plain, ![X25, X26, X27, X28, X31, X32, X33, X34, X35, X36, X38, X39]:(((((r2_hidden(esk3_4(X25,X26,X27,X28),X25)|~r2_hidden(X28,X27)|X27!=k2_zfmisc_1(X25,X26))&(r2_hidden(esk4_4(X25,X26,X27,X28),X26)|~r2_hidden(X28,X27)|X27!=k2_zfmisc_1(X25,X26)))&(X28=k4_tarski(esk3_4(X25,X26,X27,X28),esk4_4(X25,X26,X27,X28))|~r2_hidden(X28,X27)|X27!=k2_zfmisc_1(X25,X26)))&(~r2_hidden(X32,X25)|~r2_hidden(X33,X26)|X31!=k4_tarski(X32,X33)|r2_hidden(X31,X27)|X27!=k2_zfmisc_1(X25,X26)))&((~r2_hidden(esk5_3(X34,X35,X36),X36)|(~r2_hidden(X38,X34)|~r2_hidden(X39,X35)|esk5_3(X34,X35,X36)!=k4_tarski(X38,X39))|X36=k2_zfmisc_1(X34,X35))&(((r2_hidden(esk6_3(X34,X35,X36),X34)|r2_hidden(esk5_3(X34,X35,X36),X36)|X36=k2_zfmisc_1(X34,X35))&(r2_hidden(esk7_3(X34,X35,X36),X35)|r2_hidden(esk5_3(X34,X35,X36),X36)|X36=k2_zfmisc_1(X34,X35)))&(esk5_3(X34,X35,X36)=k4_tarski(esk6_3(X34,X35,X36),esk7_3(X34,X35,X36))|r2_hidden(esk5_3(X34,X35,X36),X36)|X36=k2_zfmisc_1(X34,X35))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.20/0.40  cnf(c_0_14, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.40  cnf(c_0_15, negated_conjecture, (r1_tarski(esk8_0,k2_zfmisc_1(esk9_0,esk10_0))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_16, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X3))|~r2_hidden(esk2_2(X1,k4_xboole_0(X2,X3)),X3)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.20/0.40  cnf(c_0_17, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_18, plain, (X1=k4_tarski(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_19, negated_conjecture, (r1_xboole_0(esk8_0,X1)|~r1_xboole_0(k2_zfmisc_1(esk9_0,esk10_0),X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.20/0.40  cnf(c_0_20, plain, (r1_xboole_0(X1,k4_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.40  cnf(c_0_21, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.20/0.40  cnf(c_0_22, negated_conjecture, (~r2_hidden(X1,esk9_0)|~r2_hidden(X2,esk10_0)|esk11_0!=k4_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_23, plain, (k4_tarski(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.40  cnf(c_0_24, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_25, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.40  cnf(c_0_26, negated_conjecture, (r1_xboole_0(esk8_0,k4_xboole_0(X1,k2_zfmisc_1(esk9_0,esk10_0)))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.20/0.40  cnf(c_0_27, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.40  cnf(c_0_28, negated_conjecture, (r2_hidden(esk11_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.40  cnf(c_0_29, negated_conjecture, (~r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk10_0)|~r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23])])).
% 0.20/0.40  cnf(c_0_30, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.40  cnf(c_0_31, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.40  cnf(c_0_32, negated_conjecture, (~r2_hidden(X1,k4_xboole_0(X2,k2_zfmisc_1(esk9_0,esk10_0)))|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.40  cnf(c_0_33, negated_conjecture, (r2_hidden(esk11_0,k4_xboole_0(esk8_0,X1))|r2_hidden(esk11_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.40  cnf(c_0_34, negated_conjecture, (~r2_hidden(esk3_4(X1,esk10_0,k2_zfmisc_1(X1,esk10_0),esk11_0),esk9_0)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,esk10_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.20/0.40  cnf(c_0_35, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_31])).
% 0.20/0.40  cnf(c_0_36, negated_conjecture, (r2_hidden(esk11_0,k2_zfmisc_1(esk9_0,esk10_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_28])])).
% 0.20/0.40  cnf(c_0_37, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])]), ['proof']).
% 0.20/0.40  # SZS output end CNFRefutation
% 0.20/0.40  # Proof object total steps             : 38
% 0.20/0.40  # Proof object clause steps            : 27
% 0.20/0.40  # Proof object formula steps           : 11
% 0.20/0.40  # Proof object conjectures             : 14
% 0.20/0.40  # Proof object clause conjectures      : 11
% 0.20/0.40  # Proof object formula conjectures     : 3
% 0.20/0.40  # Proof object initial clauses used    : 12
% 0.20/0.40  # Proof object initial formulas used   : 5
% 0.20/0.40  # Proof object generating inferences   : 10
% 0.20/0.40  # Proof object simplifying inferences  : 10
% 0.20/0.40  # Training examples: 0 positive, 0 negative
% 0.20/0.40  # Parsed axioms                        : 5
% 0.20/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.40  # Initial clauses                      : 21
% 0.20/0.40  # Removed in clause preprocessing      : 0
% 0.20/0.40  # Initial clauses in saturation        : 21
% 0.20/0.40  # Processed clauses                    : 442
% 0.20/0.40  # ...of these trivial                  : 7
% 0.20/0.40  # ...subsumed                          : 280
% 0.20/0.40  # ...remaining for further processing  : 155
% 0.20/0.40  # Other redundant clauses eliminated   : 9
% 0.20/0.40  # Clauses deleted for lack of memory   : 0
% 0.20/0.40  # Backward-subsumed                    : 4
% 0.20/0.40  # Backward-rewritten                   : 3
% 0.20/0.40  # Generated clauses                    : 2192
% 0.20/0.40  # ...of the previous two non-trivial   : 2000
% 0.20/0.40  # Contextual simplify-reflections      : 2
% 0.20/0.40  # Paramodulations                      : 2174
% 0.20/0.40  # Factorizations                       : 10
% 0.20/0.40  # Equation resolutions                 : 9
% 0.20/0.40  # Propositional unsat checks           : 0
% 0.20/0.40  #    Propositional check models        : 0
% 0.20/0.40  #    Propositional check unsatisfiable : 0
% 0.20/0.40  #    Propositional clauses             : 0
% 0.20/0.40  #    Propositional clauses after purity: 0
% 0.20/0.40  #    Propositional unsat core size     : 0
% 0.20/0.40  #    Propositional preprocessing time  : 0.000
% 0.20/0.40  #    Propositional encoding time       : 0.000
% 0.20/0.40  #    Propositional solver time         : 0.000
% 0.20/0.40  #    Success case prop preproc time    : 0.000
% 0.20/0.40  #    Success case prop encoding time   : 0.000
% 0.20/0.40  #    Success case prop solver time     : 0.000
% 0.20/0.40  # Current number of processed clauses  : 120
% 0.20/0.40  #    Positive orientable unit clauses  : 19
% 0.20/0.40  #    Positive unorientable unit clauses: 3
% 0.20/0.40  #    Negative unit clauses             : 20
% 0.20/0.40  #    Non-unit-clauses                  : 78
% 0.20/0.40  # Current number of unprocessed clauses: 1583
% 0.20/0.40  # ...number of literals in the above   : 4356
% 0.20/0.40  # Current number of archived formulas  : 0
% 0.20/0.40  # Current number of archived clauses   : 28
% 0.20/0.40  # Clause-clause subsumption calls (NU) : 899
% 0.20/0.40  # Rec. Clause-clause subsumption calls : 574
% 0.20/0.40  # Non-unit clause-clause subsumptions  : 57
% 0.20/0.40  # Unit Clause-clause subsumption calls : 168
% 0.20/0.40  # Rewrite failures with RHS unbound    : 128
% 0.20/0.40  # BW rewrite match attempts            : 121
% 0.20/0.40  # BW rewrite match successes           : 27
% 0.20/0.40  # Condensation attempts                : 0
% 0.20/0.40  # Condensation successes               : 0
% 0.20/0.40  # Termbank termtop insertions          : 28229
% 0.20/0.40  
% 0.20/0.40  # -------------------------------------------------
% 0.20/0.40  # User time                : 0.053 s
% 0.20/0.40  # System time              : 0.006 s
% 0.20/0.40  # Total time               : 0.059 s
% 0.20/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
