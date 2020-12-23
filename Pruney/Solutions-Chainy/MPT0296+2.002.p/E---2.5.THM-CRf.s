%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:24 EST 2020

% Result     : Theorem 0.38s
% Output     : CNFRefutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 101 expanded)
%              Number of clauses        :   24 (  51 expanded)
%              Number of leaves         :    4 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  136 ( 561 expanded)
%              Number of equality atoms :   33 ( 162 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t104_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4,X5] :
      ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
        & ! [X6,X7] :
            ~ ( X1 = k4_tarski(X6,X7)
              & r2_hidden(X6,k3_xboole_0(X2,X4))
              & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_zfmisc_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

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

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2,X3,X4,X5] :
        ~ ( r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))
          & ! [X6,X7] :
              ~ ( X1 = k4_tarski(X6,X7)
                & r2_hidden(X6,k3_xboole_0(X2,X4))
                & r2_hidden(X7,k3_xboole_0(X3,X5)) ) ) ),
    inference(assume_negation,[status(cth)],[t104_zfmisc_1])).

fof(c_0_5,plain,(
    ! [X17,X18,X19,X20,X21,X22,X23,X24] :
      ( ( r2_hidden(X20,X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( ~ r2_hidden(X21,X17)
        | ~ r2_hidden(X21,X18)
        | r2_hidden(X21,X19)
        | X19 != k3_xboole_0(X17,X18) )
      & ( ~ r2_hidden(esk2_3(X22,X23,X24),X24)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X22)
        | ~ r2_hidden(esk2_3(X22,X23,X24),X23)
        | X24 = k3_xboole_0(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X22)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k3_xboole_0(X22,X23) )
      & ( r2_hidden(esk2_3(X22,X23,X24),X23)
        | r2_hidden(esk2_3(X22,X23,X24),X24)
        | X24 = k3_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_6,plain,(
    ! [X33,X34,X35,X36,X39,X40,X41,X42,X43,X44,X46,X47] :
      ( ( r2_hidden(esk4_4(X33,X34,X35,X36),X33)
        | ~ r2_hidden(X36,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( r2_hidden(esk5_4(X33,X34,X35,X36),X34)
        | ~ r2_hidden(X36,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( X36 = k4_tarski(esk4_4(X33,X34,X35,X36),esk5_4(X33,X34,X35,X36))
        | ~ r2_hidden(X36,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( ~ r2_hidden(X40,X33)
        | ~ r2_hidden(X41,X34)
        | X39 != k4_tarski(X40,X41)
        | r2_hidden(X39,X35)
        | X35 != k2_zfmisc_1(X33,X34) )
      & ( ~ r2_hidden(esk6_3(X42,X43,X44),X44)
        | ~ r2_hidden(X46,X42)
        | ~ r2_hidden(X47,X43)
        | esk6_3(X42,X43,X44) != k4_tarski(X46,X47)
        | X44 = k2_zfmisc_1(X42,X43) )
      & ( r2_hidden(esk7_3(X42,X43,X44),X42)
        | r2_hidden(esk6_3(X42,X43,X44),X44)
        | X44 = k2_zfmisc_1(X42,X43) )
      & ( r2_hidden(esk8_3(X42,X43,X44),X43)
        | r2_hidden(esk6_3(X42,X43,X44),X44)
        | X44 = k2_zfmisc_1(X42,X43) )
      & ( esk6_3(X42,X43,X44) = k4_tarski(esk7_3(X42,X43,X44),esk8_3(X42,X43,X44))
        | r2_hidden(esk6_3(X42,X43,X44),X44)
        | X44 = k2_zfmisc_1(X42,X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X61,X62] :
      ( r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))
      & ( esk9_0 != k4_tarski(X61,X62)
        | ~ r2_hidden(X61,k3_xboole_0(esk10_0,esk12_0))
        | ~ r2_hidden(X62,k3_xboole_0(esk11_0,esk13_0)) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).

cnf(c_0_8,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_9,plain,(
    ! [X50,X51,X52,X53] :
      ( ( r2_hidden(X50,X52)
        | ~ r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) )
      & ( r2_hidden(X51,X53)
        | ~ r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) )
      & ( ~ r2_hidden(X50,X52)
        | ~ r2_hidden(X51,X53)
        | r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

cnf(c_0_10,plain,
    ( X1 = k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_12,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_13,negated_conjecture,
    ( esk9_0 != k4_tarski(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))
    | ~ r2_hidden(X2,k3_xboole_0(esk11_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( k4_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_17,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))
    | ~ r2_hidden(X2,esk13_0)
    | ~ r2_hidden(X2,esk11_0) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X4,X5))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(esk10_0,esk11_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk9_0,k2_zfmisc_1(esk12_0,esk13_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)
    | ~ r2_hidden(X3,k2_zfmisc_1(X5,X4))
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( k4_tarski(X1,X2) != esk9_0
    | ~ r2_hidden(X2,esk13_0)
    | ~ r2_hidden(X2,esk11_0)
    | ~ r2_hidden(X1,esk12_0)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk10_0)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk12_0)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk11_0)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk13_0)
    | ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( ~ r2_hidden(esk9_0,k2_zfmisc_1(X1,X2)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16])]),c_0_27]),c_0_28]),c_0_29]),c_0_30])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_24,c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:34:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.38/0.62  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.38/0.62  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.38/0.62  #
% 0.38/0.62  # Preprocessing time       : 0.028 s
% 0.38/0.62  # Presaturation interreduction done
% 0.38/0.62  
% 0.38/0.62  # Proof found!
% 0.38/0.62  # SZS status Theorem
% 0.38/0.62  # SZS output start CNFRefutation
% 0.38/0.62  fof(t104_zfmisc_1, conjecture, ![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_zfmisc_1)).
% 0.38/0.62  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.38/0.62  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.38/0.62  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.38/0.62  fof(c_0_4, negated_conjecture, ~(![X1, X2, X3, X4, X5]:~((r2_hidden(X1,k3_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X5)))&![X6, X7]:~(((X1=k4_tarski(X6,X7)&r2_hidden(X6,k3_xboole_0(X2,X4)))&r2_hidden(X7,k3_xboole_0(X3,X5))))))), inference(assume_negation,[status(cth)],[t104_zfmisc_1])).
% 0.38/0.62  fof(c_0_5, plain, ![X17, X18, X19, X20, X21, X22, X23, X24]:((((r2_hidden(X20,X17)|~r2_hidden(X20,X19)|X19!=k3_xboole_0(X17,X18))&(r2_hidden(X20,X18)|~r2_hidden(X20,X19)|X19!=k3_xboole_0(X17,X18)))&(~r2_hidden(X21,X17)|~r2_hidden(X21,X18)|r2_hidden(X21,X19)|X19!=k3_xboole_0(X17,X18)))&((~r2_hidden(esk2_3(X22,X23,X24),X24)|(~r2_hidden(esk2_3(X22,X23,X24),X22)|~r2_hidden(esk2_3(X22,X23,X24),X23))|X24=k3_xboole_0(X22,X23))&((r2_hidden(esk2_3(X22,X23,X24),X22)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k3_xboole_0(X22,X23))&(r2_hidden(esk2_3(X22,X23,X24),X23)|r2_hidden(esk2_3(X22,X23,X24),X24)|X24=k3_xboole_0(X22,X23))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.38/0.62  fof(c_0_6, plain, ![X33, X34, X35, X36, X39, X40, X41, X42, X43, X44, X46, X47]:(((((r2_hidden(esk4_4(X33,X34,X35,X36),X33)|~r2_hidden(X36,X35)|X35!=k2_zfmisc_1(X33,X34))&(r2_hidden(esk5_4(X33,X34,X35,X36),X34)|~r2_hidden(X36,X35)|X35!=k2_zfmisc_1(X33,X34)))&(X36=k4_tarski(esk4_4(X33,X34,X35,X36),esk5_4(X33,X34,X35,X36))|~r2_hidden(X36,X35)|X35!=k2_zfmisc_1(X33,X34)))&(~r2_hidden(X40,X33)|~r2_hidden(X41,X34)|X39!=k4_tarski(X40,X41)|r2_hidden(X39,X35)|X35!=k2_zfmisc_1(X33,X34)))&((~r2_hidden(esk6_3(X42,X43,X44),X44)|(~r2_hidden(X46,X42)|~r2_hidden(X47,X43)|esk6_3(X42,X43,X44)!=k4_tarski(X46,X47))|X44=k2_zfmisc_1(X42,X43))&(((r2_hidden(esk7_3(X42,X43,X44),X42)|r2_hidden(esk6_3(X42,X43,X44),X44)|X44=k2_zfmisc_1(X42,X43))&(r2_hidden(esk8_3(X42,X43,X44),X43)|r2_hidden(esk6_3(X42,X43,X44),X44)|X44=k2_zfmisc_1(X42,X43)))&(esk6_3(X42,X43,X44)=k4_tarski(esk7_3(X42,X43,X44),esk8_3(X42,X43,X44))|r2_hidden(esk6_3(X42,X43,X44),X44)|X44=k2_zfmisc_1(X42,X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.38/0.62  fof(c_0_7, negated_conjecture, ![X61, X62]:(r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))&(esk9_0!=k4_tarski(X61,X62)|~r2_hidden(X61,k3_xboole_0(esk10_0,esk12_0))|~r2_hidden(X62,k3_xboole_0(esk11_0,esk13_0)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])])).
% 0.38/0.62  cnf(c_0_8, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X4!=k3_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.38/0.62  fof(c_0_9, plain, ![X50, X51, X52, X53]:(((r2_hidden(X50,X52)|~r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)))&(r2_hidden(X51,X53)|~r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53))))&(~r2_hidden(X50,X52)|~r2_hidden(X51,X53)|r2_hidden(k4_tarski(X50,X51),k2_zfmisc_1(X52,X53)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.38/0.62  cnf(c_0_10, plain, (X1=k4_tarski(esk4_4(X2,X3,X4,X1),esk5_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.38/0.62  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.38/0.62  cnf(c_0_12, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k3_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.38/0.62  cnf(c_0_13, negated_conjecture, (esk9_0!=k4_tarski(X1,X2)|~r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))|~r2_hidden(X2,k3_xboole_0(esk11_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.38/0.62  cnf(c_0_14, plain, (r2_hidden(X1,k3_xboole_0(X2,X3))|~r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_8])).
% 0.38/0.62  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.38/0.62  cnf(c_0_16, plain, (k4_tarski(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.38/0.62  cnf(c_0_17, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_11])).
% 0.38/0.62  cnf(c_0_18, negated_conjecture, (r2_hidden(esk9_0,k3_xboole_0(k2_zfmisc_1(esk10_0,esk11_0),k2_zfmisc_1(esk12_0,esk13_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.38/0.62  cnf(c_0_19, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k3_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_12])).
% 0.38/0.62  cnf(c_0_20, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.38/0.62  cnf(c_0_21, negated_conjecture, (k4_tarski(X1,X2)!=esk9_0|~r2_hidden(X1,k3_xboole_0(esk10_0,esk12_0))|~r2_hidden(X2,esk13_0)|~r2_hidden(X2,esk11_0)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.38/0.62  cnf(c_0_22, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)|~r2_hidden(X3,k2_zfmisc_1(X4,X5))|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.38/0.62  cnf(c_0_23, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(esk10_0,esk11_0))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.38/0.62  cnf(c_0_24, negated_conjecture, (r2_hidden(esk9_0,k2_zfmisc_1(esk12_0,esk13_0))), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.38/0.62  cnf(c_0_25, plain, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X4)|~r2_hidden(X3,k2_zfmisc_1(X5,X4))|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_20, c_0_16])).
% 0.38/0.62  cnf(c_0_26, negated_conjecture, (k4_tarski(X1,X2)!=esk9_0|~r2_hidden(X2,esk13_0)|~r2_hidden(X2,esk11_0)|~r2_hidden(X1,esk12_0)|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_21, c_0_14])).
% 0.38/0.62  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk10_0)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.38/0.62  cnf(c_0_28, negated_conjecture, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk12_0)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_22, c_0_24])).
% 0.38/0.62  cnf(c_0_29, negated_conjecture, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk11_0)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_23])).
% 0.38/0.62  cnf(c_0_30, negated_conjecture, (r2_hidden(esk5_4(X1,X2,k2_zfmisc_1(X1,X2),esk9_0),esk13_0)|~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_25, c_0_24])).
% 0.38/0.62  cnf(c_0_31, negated_conjecture, (~r2_hidden(esk9_0,k2_zfmisc_1(X1,X2))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16])]), c_0_27]), c_0_28]), c_0_29]), c_0_30])).
% 0.38/0.62  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_24, c_0_31]), ['proof']).
% 0.38/0.62  # SZS output end CNFRefutation
% 0.38/0.62  # Proof object total steps             : 33
% 0.38/0.62  # Proof object clause steps            : 24
% 0.38/0.62  # Proof object formula steps           : 9
% 0.38/0.62  # Proof object conjectures             : 15
% 0.38/0.62  # Proof object clause conjectures      : 12
% 0.38/0.62  # Proof object formula conjectures     : 3
% 0.38/0.62  # Proof object initial clauses used    : 8
% 0.38/0.62  # Proof object initial formulas used   : 4
% 0.38/0.62  # Proof object generating inferences   : 11
% 0.38/0.62  # Proof object simplifying inferences  : 10
% 0.38/0.62  # Training examples: 0 positive, 0 negative
% 0.38/0.62  # Parsed axioms                        : 7
% 0.38/0.62  # Removed by relevancy pruning/SinE    : 0
% 0.38/0.62  # Initial clauses                      : 30
% 0.38/0.62  # Removed in clause preprocessing      : 0
% 0.38/0.62  # Initial clauses in saturation        : 30
% 0.38/0.62  # Processed clauses                    : 1359
% 0.38/0.62  # ...of these trivial                  : 8
% 0.38/0.62  # ...subsumed                          : 906
% 0.38/0.62  # ...remaining for further processing  : 445
% 0.38/0.62  # Other redundant clauses eliminated   : 21
% 0.38/0.62  # Clauses deleted for lack of memory   : 0
% 0.38/0.62  # Backward-subsumed                    : 4
% 0.38/0.62  # Backward-rewritten                   : 2
% 0.38/0.62  # Generated clauses                    : 21601
% 0.38/0.62  # ...of the previous two non-trivial   : 20503
% 0.38/0.62  # Contextual simplify-reflections      : 7
% 0.38/0.62  # Paramodulations                      : 21432
% 0.38/0.62  # Factorizations                       : 148
% 0.38/0.62  # Equation resolutions                 : 21
% 0.38/0.62  # Propositional unsat checks           : 0
% 0.38/0.62  #    Propositional check models        : 0
% 0.38/0.62  #    Propositional check unsatisfiable : 0
% 0.38/0.62  #    Propositional clauses             : 0
% 0.38/0.62  #    Propositional clauses after purity: 0
% 0.38/0.62  #    Propositional unsat core size     : 0
% 0.38/0.62  #    Propositional preprocessing time  : 0.000
% 0.38/0.62  #    Propositional encoding time       : 0.000
% 0.38/0.62  #    Propositional solver time         : 0.000
% 0.38/0.62  #    Success case prop preproc time    : 0.000
% 0.38/0.62  #    Success case prop encoding time   : 0.000
% 0.38/0.62  #    Success case prop solver time     : 0.000
% 0.38/0.62  # Current number of processed clauses  : 396
% 0.38/0.62  #    Positive orientable unit clauses  : 85
% 0.38/0.62  #    Positive unorientable unit clauses: 0
% 0.38/0.62  #    Negative unit clauses             : 6
% 0.38/0.62  #    Non-unit-clauses                  : 305
% 0.38/0.62  # Current number of unprocessed clauses: 19167
% 0.38/0.62  # ...number of literals in the above   : 75119
% 0.38/0.62  # Current number of archived formulas  : 0
% 0.38/0.62  # Current number of archived clauses   : 37
% 0.38/0.62  # Clause-clause subsumption calls (NU) : 31105
% 0.38/0.62  # Rec. Clause-clause subsumption calls : 21571
% 0.38/0.62  # Non-unit clause-clause subsumptions  : 905
% 0.38/0.62  # Unit Clause-clause subsumption calls : 2156
% 0.38/0.62  # Rewrite failures with RHS unbound    : 0
% 0.38/0.62  # BW rewrite match attempts            : 279
% 0.38/0.62  # BW rewrite match successes           : 2
% 0.38/0.62  # Condensation attempts                : 0
% 0.38/0.62  # Condensation successes               : 0
% 0.38/0.62  # Termbank termtop insertions          : 403189
% 0.38/0.62  
% 0.38/0.62  # -------------------------------------------------
% 0.38/0.62  # User time                : 0.275 s
% 0.38/0.62  # System time              : 0.016 s
% 0.38/0.62  # Total time               : 0.291 s
% 0.38/0.62  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
