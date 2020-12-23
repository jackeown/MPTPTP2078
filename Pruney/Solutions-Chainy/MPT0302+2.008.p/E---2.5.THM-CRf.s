%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:32 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 136 expanded)
%              Number of clauses        :   41 (  62 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 499 expanded)
%              Number of equality atoms :   56 ( 201 expanded)
%              Maximal formula depth    :   23 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t114_zfmisc_1,conjecture,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
     => ( X1 = k1_xboole_0
        | X2 = k1_xboole_0
        | X1 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(l54_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X4) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(c_0_8,plain,(
    ! [X19,X20,X21,X22,X25,X26,X27,X28,X29,X30,X32,X33] :
      ( ( r2_hidden(esk3_4(X19,X20,X21,X22),X19)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( r2_hidden(esk4_4(X19,X20,X21,X22),X20)
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( X22 = k4_tarski(esk3_4(X19,X20,X21,X22),esk4_4(X19,X20,X21,X22))
        | ~ r2_hidden(X22,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(X26,X19)
        | ~ r2_hidden(X27,X20)
        | X25 != k4_tarski(X26,X27)
        | r2_hidden(X25,X21)
        | X21 != k2_zfmisc_1(X19,X20) )
      & ( ~ r2_hidden(esk5_3(X28,X29,X30),X30)
        | ~ r2_hidden(X32,X28)
        | ~ r2_hidden(X33,X29)
        | esk5_3(X28,X29,X30) != k4_tarski(X32,X33)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk6_3(X28,X29,X30),X28)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( r2_hidden(esk7_3(X28,X29,X30),X29)
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) )
      & ( esk5_3(X28,X29,X30) = k4_tarski(esk6_3(X28,X29,X30),esk7_3(X28,X29,X30))
        | r2_hidden(esk5_3(X28,X29,X30),X30)
        | X30 = k2_zfmisc_1(X28,X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_10,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_12,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_10])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( k2_zfmisc_1(X1,X2) = k2_zfmisc_1(X2,X1)
       => ( X1 = k1_xboole_0
          | X2 = k1_xboole_0
          | X1 = X2 ) ) ),
    inference(assume_negation,[status(cth)],[t114_zfmisc_1])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_18,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk9_0,esk8_0)
    & esk8_0 != k1_xboole_0
    & esk9_0 != k1_xboole_0
    & esk8_0 != esk9_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X36,X37,X38,X39] :
      ( ( r2_hidden(X36,X38)
        | ~ r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(X38,X39)) )
      & ( r2_hidden(X37,X39)
        | ~ r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(X38,X39)) )
      & ( ~ r2_hidden(X36,X38)
        | ~ r2_hidden(X37,X39)
        | r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(X38,X39)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).

fof(c_0_20,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_12,c_0_15])).

cnf(c_0_22,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_23,plain,
    ( v1_xboole_0(k2_zfmisc_1(X1,X2))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( k2_zfmisc_1(esk8_0,esk9_0) = k2_zfmisc_1(esk9_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X40,X41] :
      ( ( k2_zfmisc_1(X40,X41) != k1_xboole_0
        | X40 = k1_xboole_0
        | X41 = k1_xboole_0 )
      & ( X40 != k1_xboole_0
        | k2_zfmisc_1(X40,X41) = k1_xboole_0 )
      & ( X41 != k1_xboole_0
        | k2_zfmisc_1(X40,X41) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( v1_xboole_0(k2_zfmisc_1(esk9_0,esk8_0))
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_zfmisc_1(X1,X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,negated_conjecture,
    ( esk8_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_35,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( r1_tarski(k2_zfmisc_1(esk9_0,esk8_0),X1)
    | ~ v1_xboole_0(esk8_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( k2_zfmisc_1(esk9_0,esk8_0) != k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_24]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_39,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( ~ v1_xboole_0(esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk9_0,esk8_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_24])).

cnf(c_0_43,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_17]),c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(X1,esk9_0)
    | ~ r2_hidden(X1,esk8_0)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_34])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_43]),c_0_22])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X1)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_49,negated_conjecture,
    ( r1_tarski(X1,esk8_0)
    | ~ r2_hidden(esk2_2(X1,esk8_0),esk9_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),esk9_0)
    | ~ r2_hidden(X2,esk9_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_15])).

cnf(c_0_51,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk9_0,esk8_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( esk8_0 != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(esk8_0,X1)
    | r2_hidden(esk2_2(esk8_0,X1),esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31])).

cnf(c_0_55,negated_conjecture,
    ( ~ r1_tarski(esk8_0,esk9_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_52]),c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.12/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.12/0.39  #
% 0.12/0.39  # Preprocessing time       : 0.028 s
% 0.12/0.39  # Presaturation interreduction done
% 0.12/0.39  
% 0.12/0.39  # Proof found!
% 0.12/0.39  # SZS status Theorem
% 0.12/0.39  # SZS output start CNFRefutation
% 0.12/0.39  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.12/0.39  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.12/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.12/0.39  fof(t114_zfmisc_1, conjecture, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 0.12/0.39  fof(l54_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(X3,X4))<=>(r2_hidden(X1,X3)&r2_hidden(X2,X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 0.12/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.12/0.39  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.39  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.12/0.39  fof(c_0_8, plain, ![X19, X20, X21, X22, X25, X26, X27, X28, X29, X30, X32, X33]:(((((r2_hidden(esk3_4(X19,X20,X21,X22),X19)|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20))&(r2_hidden(esk4_4(X19,X20,X21,X22),X20)|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20)))&(X22=k4_tarski(esk3_4(X19,X20,X21,X22),esk4_4(X19,X20,X21,X22))|~r2_hidden(X22,X21)|X21!=k2_zfmisc_1(X19,X20)))&(~r2_hidden(X26,X19)|~r2_hidden(X27,X20)|X25!=k4_tarski(X26,X27)|r2_hidden(X25,X21)|X21!=k2_zfmisc_1(X19,X20)))&((~r2_hidden(esk5_3(X28,X29,X30),X30)|(~r2_hidden(X32,X28)|~r2_hidden(X33,X29)|esk5_3(X28,X29,X30)!=k4_tarski(X32,X33))|X30=k2_zfmisc_1(X28,X29))&(((r2_hidden(esk6_3(X28,X29,X30),X28)|r2_hidden(esk5_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29))&(r2_hidden(esk7_3(X28,X29,X30),X29)|r2_hidden(esk5_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29)))&(esk5_3(X28,X29,X30)=k4_tarski(esk6_3(X28,X29,X30),esk7_3(X28,X29,X30))|r2_hidden(esk5_3(X28,X29,X30),X30)|X30=k2_zfmisc_1(X28,X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.12/0.39  fof(c_0_9, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.12/0.39  cnf(c_0_10, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  fof(c_0_11, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.12/0.39  cnf(c_0_12, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  cnf(c_0_13, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_10])).
% 0.12/0.39  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(k2_zfmisc_1(X1,X2)=k2_zfmisc_1(X2,X1)=>(X1=k1_xboole_0|X2=k1_xboole_0|X1=X2))), inference(assume_negation,[status(cth)],[t114_zfmisc_1])).
% 0.12/0.39  cnf(c_0_15, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_16, plain, (~r2_hidden(X1,k2_zfmisc_1(X2,X3))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.12/0.39  cnf(c_0_17, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.12/0.39  fof(c_0_18, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk9_0,esk8_0)&((esk8_0!=k1_xboole_0&esk9_0!=k1_xboole_0)&esk8_0!=esk9_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.12/0.39  fof(c_0_19, plain, ![X36, X37, X38, X39]:(((r2_hidden(X36,X38)|~r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(X38,X39)))&(r2_hidden(X37,X39)|~r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(X38,X39))))&(~r2_hidden(X36,X38)|~r2_hidden(X37,X39)|r2_hidden(k4_tarski(X36,X37),k2_zfmisc_1(X38,X39)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l54_zfmisc_1])])])).
% 0.12/0.39  fof(c_0_20, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.12/0.39  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_12, c_0_15])).
% 0.12/0.39  cnf(c_0_22, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.39  cnf(c_0_23, plain, (v1_xboole_0(k2_zfmisc_1(X1,X2))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.12/0.39  cnf(c_0_24, negated_conjecture, (k2_zfmisc_1(esk8_0,esk9_0)=k2_zfmisc_1(esk9_0,esk8_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  fof(c_0_25, plain, ![X40, X41]:((k2_zfmisc_1(X40,X41)!=k1_xboole_0|(X40=k1_xboole_0|X41=k1_xboole_0))&((X40!=k1_xboole_0|k2_zfmisc_1(X40,X41)=k1_xboole_0)&(X41!=k1_xboole_0|k2_zfmisc_1(X40,X41)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.12/0.39  cnf(c_0_26, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_27, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.12/0.39  cnf(c_0_28, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.12/0.39  cnf(c_0_29, negated_conjecture, (v1_xboole_0(k2_zfmisc_1(esk9_0,esk8_0))|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.39  cnf(c_0_30, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k2_zfmisc_1(X1,X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_31, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_32, negated_conjecture, (esk8_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_33, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_26, c_0_24])).
% 0.12/0.39  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(X2,X4))|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_35, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.12/0.39  cnf(c_0_36, negated_conjecture, (r1_tarski(k2_zfmisc_1(esk9_0,esk8_0),X1)|~v1_xboole_0(esk8_0)), inference(spm,[status(thm)],[c_0_21, c_0_29])).
% 0.12/0.39  cnf(c_0_37, negated_conjecture, (k2_zfmisc_1(esk9_0,esk8_0)!=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_24]), c_0_31]), c_0_32])).
% 0.12/0.39  cnf(c_0_38, plain, (r2_hidden(X1,X2)|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(X4,X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.39  cnf(c_0_39, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.39  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk8_0)|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.39  cnf(c_0_41, negated_conjecture, (~v1_xboole_0(esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])).
% 0.12/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(esk9_0,esk8_0))), inference(spm,[status(thm)],[c_0_38, c_0_24])).
% 0.12/0.39  cnf(c_0_43, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_39])).
% 0.12/0.39  cnf(c_0_44, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.39  cnf(c_0_45, negated_conjecture, (r2_hidden(X1,esk8_0)|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_17]), c_0_41])).
% 0.12/0.39  cnf(c_0_46, negated_conjecture, (r2_hidden(X1,esk9_0)|~r2_hidden(X1,esk8_0)|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_42, c_0_34])).
% 0.12/0.39  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_43]), c_0_22])])).
% 0.12/0.39  cnf(c_0_48, plain, (r2_hidden(esk6_3(X1,X2,X3),X1)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.12/0.39  cnf(c_0_49, negated_conjecture, (r1_tarski(X1,esk8_0)|~r2_hidden(esk2_2(X1,esk8_0),esk9_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.12/0.39  cnf(c_0_50, negated_conjecture, (r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),esk9_0)|~r2_hidden(X2,esk9_0)), inference(spm,[status(thm)],[c_0_46, c_0_15])).
% 0.12/0.39  cnf(c_0_51, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(k1_xboole_0,X2,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_43])).
% 0.12/0.39  cnf(c_0_52, negated_conjecture, (r1_tarski(esk9_0,esk8_0)), inference(spm,[status(thm)],[c_0_49, c_0_15])).
% 0.12/0.39  cnf(c_0_53, negated_conjecture, (esk8_0!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.39  cnf(c_0_54, negated_conjecture, (r1_tarski(esk8_0,X1)|r2_hidden(esk2_2(esk8_0,X1),esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_31])).
% 0.12/0.39  cnf(c_0_55, negated_conjecture, (~r1_tarski(esk8_0,esk9_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_52]), c_0_53])).
% 0.12/0.39  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_55]), ['proof']).
% 0.12/0.39  # SZS output end CNFRefutation
% 0.12/0.39  # Proof object total steps             : 57
% 0.12/0.39  # Proof object clause steps            : 41
% 0.12/0.39  # Proof object formula steps           : 16
% 0.12/0.39  # Proof object conjectures             : 22
% 0.12/0.39  # Proof object clause conjectures      : 19
% 0.12/0.39  # Proof object formula conjectures     : 3
% 0.12/0.39  # Proof object initial clauses used    : 17
% 0.12/0.39  # Proof object initial formulas used   : 8
% 0.12/0.39  # Proof object generating inferences   : 22
% 0.12/0.39  # Proof object simplifying inferences  : 12
% 0.12/0.39  # Training examples: 0 positive, 0 negative
% 0.12/0.39  # Parsed axioms                        : 8
% 0.12/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.39  # Initial clauses                      : 27
% 0.12/0.39  # Removed in clause preprocessing      : 0
% 0.12/0.39  # Initial clauses in saturation        : 27
% 0.12/0.39  # Processed clauses                    : 529
% 0.12/0.39  # ...of these trivial                  : 0
% 0.12/0.39  # ...subsumed                          : 372
% 0.12/0.39  # ...remaining for further processing  : 157
% 0.12/0.39  # Other redundant clauses eliminated   : 9
% 0.12/0.39  # Clauses deleted for lack of memory   : 0
% 0.12/0.39  # Backward-subsumed                    : 13
% 0.12/0.39  # Backward-rewritten                   : 6
% 0.12/0.39  # Generated clauses                    : 1217
% 0.12/0.39  # ...of the previous two non-trivial   : 920
% 0.12/0.39  # Contextual simplify-reflections      : 0
% 0.12/0.39  # Paramodulations                      : 1209
% 0.12/0.39  # Factorizations                       : 0
% 0.12/0.39  # Equation resolutions                 : 9
% 0.12/0.39  # Propositional unsat checks           : 0
% 0.12/0.39  #    Propositional check models        : 0
% 0.12/0.39  #    Propositional check unsatisfiable : 0
% 0.12/0.39  #    Propositional clauses             : 0
% 0.12/0.39  #    Propositional clauses after purity: 0
% 0.12/0.39  #    Propositional unsat core size     : 0
% 0.12/0.39  #    Propositional preprocessing time  : 0.000
% 0.12/0.39  #    Propositional encoding time       : 0.000
% 0.12/0.39  #    Propositional solver time         : 0.000
% 0.12/0.39  #    Success case prop preproc time    : 0.000
% 0.12/0.39  #    Success case prop encoding time   : 0.000
% 0.12/0.39  #    Success case prop solver time     : 0.000
% 0.12/0.39  # Current number of processed clauses  : 105
% 0.12/0.39  #    Positive orientable unit clauses  : 10
% 0.12/0.39  #    Positive unorientable unit clauses: 0
% 0.12/0.39  #    Negative unit clauses             : 8
% 0.12/0.39  #    Non-unit-clauses                  : 87
% 0.12/0.39  # Current number of unprocessed clauses: 392
% 0.12/0.39  # ...number of literals in the above   : 1320
% 0.12/0.39  # Current number of archived formulas  : 0
% 0.12/0.39  # Current number of archived clauses   : 44
% 0.12/0.39  # Clause-clause subsumption calls (NU) : 1460
% 0.12/0.39  # Rec. Clause-clause subsumption calls : 1205
% 0.12/0.39  # Non-unit clause-clause subsumptions  : 124
% 0.12/0.39  # Unit Clause-clause subsumption calls : 71
% 0.12/0.39  # Rewrite failures with RHS unbound    : 0
% 0.12/0.39  # BW rewrite match attempts            : 3
% 0.12/0.39  # BW rewrite match successes           : 3
% 0.12/0.39  # Condensation attempts                : 0
% 0.12/0.39  # Condensation successes               : 0
% 0.12/0.39  # Termbank termtop insertions          : 14146
% 0.12/0.39  
% 0.12/0.39  # -------------------------------------------------
% 0.12/0.39  # User time                : 0.047 s
% 0.12/0.39  # System time              : 0.005 s
% 0.12/0.39  # Total time               : 0.052 s
% 0.12/0.39  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
