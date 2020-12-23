%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:56 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 406 expanded)
%              Number of clauses        :   25 ( 196 expanded)
%              Number of leaves         :    6 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :   98 (1650 expanded)
%              Number of equality atoms :   29 ( 285 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t46_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t83_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
    <=> k4_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(t2_zfmisc_1,conjecture,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(c_0_6,plain,(
    ! [X5,X6,X8,X9,X10] :
      ( ( r2_hidden(esk1_2(X5,X6),X5)
        | r1_xboole_0(X5,X6) )
      & ( r2_hidden(esk1_2(X5,X6),X6)
        | r1_xboole_0(X5,X6) )
      & ( ~ r2_hidden(X10,X8)
        | ~ r2_hidden(X10,X9)
        | ~ r1_xboole_0(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_7,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k2_xboole_0(X14,X15)) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t46_xboole_1])).

fof(c_0_8,plain,(
    ! [X13] : k2_xboole_0(X13,k1_xboole_0) = X13 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_9,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X16,X17] :
      ( ( ~ r1_xboole_0(X16,X17)
        | k4_xboole_0(X16,X17) = X16 )
      & ( k4_xboole_0(X16,X17) != X16
        | r1_xboole_0(X16,X17) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).

cnf(c_0_12,plain,
    ( k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_14,plain,(
    ! [X18,X19,X20,X22,X23,X24,X25,X27] :
      ( ( r2_hidden(X20,esk3_3(X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k3_tarski(X18) )
      & ( r2_hidden(esk3_3(X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k3_tarski(X18) )
      & ( ~ r2_hidden(X22,X23)
        | ~ r2_hidden(X23,X18)
        | r2_hidden(X22,X19)
        | X19 != k3_tarski(X18) )
      & ( ~ r2_hidden(esk4_2(X24,X25),X25)
        | ~ r2_hidden(esk4_2(X24,X25),X27)
        | ~ r2_hidden(X27,X24)
        | X25 = k3_tarski(X24) )
      & ( r2_hidden(esk4_2(X24,X25),esk5_2(X24,X25))
        | r2_hidden(esk4_2(X24,X25),X25)
        | X25 = k3_tarski(X24) )
      & ( r2_hidden(esk5_2(X24,X25),X24)
        | r2_hidden(esk4_2(X24,X25),X25)
        | X25 = k3_tarski(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_16,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X2)
    | k4_xboole_0(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_19,plain,
    ( r2_hidden(esk5_2(X1,X2),X1)
    | r2_hidden(esk4_2(X1,X2),X2)
    | X2 = k3_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_9,c_0_15])).

cnf(c_0_21,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_10])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18])])).

cnf(c_0_23,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X1)
    | ~ r2_hidden(esk5_2(X2,X1),X3)
    | ~ r1_xboole_0(X3,X2) ),
    inference(spm,[status(thm)],[c_0_9,c_0_19])).

cnf(c_0_24,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_10])).

cnf(c_0_25,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_26,plain,
    ( X1 = k3_tarski(X2)
    | r2_hidden(esk4_2(X2,X1),X1)
    | ~ r1_xboole_0(X2,X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19])).

cnf(c_0_27,plain,
    ( r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_28,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t2_zfmisc_1])).

cnf(c_0_29,plain,
    ( X2 = k3_tarski(X1)
    | ~ r2_hidden(esk4_2(X1,X2),X2)
    | ~ r2_hidden(esk4_2(X1,X2),X3)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | r2_hidden(esk4_2(k1_xboole_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_31,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_28])).

cnf(c_0_32,plain,
    ( X1 = k3_tarski(k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_34,plain,
    ( esk4_2(k1_xboole_0,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_33])).

cnf(c_0_35,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_34]),c_0_25])]),c_0_33])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(k3_tarski(k1_xboole_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_35]),c_0_25])])).

cnf(c_0_37,plain,
    ( $false ),
    inference(sr,[status(thm)],[c_0_35,c_0_36]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:54:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S03FN
% 0.13/0.36  # and selection function PSelectLComplex.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.022 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.36  fof(t46_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 0.13/0.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.13/0.36  fof(t83_xboole_1, axiom, ![X1, X2]:(r1_xboole_0(X1,X2)<=>k4_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 0.13/0.36  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 0.13/0.36  fof(t2_zfmisc_1, conjecture, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.13/0.36  fof(c_0_6, plain, ![X5, X6, X8, X9, X10]:(((r2_hidden(esk1_2(X5,X6),X5)|r1_xboole_0(X5,X6))&(r2_hidden(esk1_2(X5,X6),X6)|r1_xboole_0(X5,X6)))&(~r2_hidden(X10,X8)|~r2_hidden(X10,X9)|~r1_xboole_0(X8,X9))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.36  fof(c_0_7, plain, ![X14, X15]:k4_xboole_0(X14,k2_xboole_0(X14,X15))=k1_xboole_0, inference(variable_rename,[status(thm)],[t46_xboole_1])).
% 0.13/0.36  fof(c_0_8, plain, ![X13]:k2_xboole_0(X13,k1_xboole_0)=X13, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.13/0.36  cnf(c_0_9, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_10, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  fof(c_0_11, plain, ![X16, X17]:((~r1_xboole_0(X16,X17)|k4_xboole_0(X16,X17)=X16)&(k4_xboole_0(X16,X17)!=X16|r1_xboole_0(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t83_xboole_1])])).
% 0.13/0.36  cnf(c_0_12, plain, (k4_xboole_0(X1,k2_xboole_0(X1,X2))=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.36  cnf(c_0_13, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  fof(c_0_14, plain, ![X18, X19, X20, X22, X23, X24, X25, X27]:((((r2_hidden(X20,esk3_3(X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k3_tarski(X18))&(r2_hidden(esk3_3(X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k3_tarski(X18)))&(~r2_hidden(X22,X23)|~r2_hidden(X23,X18)|r2_hidden(X22,X19)|X19!=k3_tarski(X18)))&((~r2_hidden(esk4_2(X24,X25),X25)|(~r2_hidden(esk4_2(X24,X25),X27)|~r2_hidden(X27,X24))|X25=k3_tarski(X24))&((r2_hidden(esk4_2(X24,X25),esk5_2(X24,X25))|r2_hidden(esk4_2(X24,X25),X25)|X25=k3_tarski(X24))&(r2_hidden(esk5_2(X24,X25),X24)|r2_hidden(esk4_2(X24,X25),X25)|X25=k3_tarski(X24))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.13/0.36  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.36  cnf(c_0_16, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.36  cnf(c_0_17, plain, (r1_xboole_0(X1,X2)|k4_xboole_0(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_18, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.36  cnf(c_0_19, plain, (r2_hidden(esk5_2(X1,X2),X1)|r2_hidden(esk4_2(X1,X2),X2)|X2=k3_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_20, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_9, c_0_15])).
% 0.13/0.36  cnf(c_0_21, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_16, c_0_10])).
% 0.13/0.36  cnf(c_0_22, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18])])).
% 0.13/0.36  cnf(c_0_23, plain, (X1=k3_tarski(X2)|r2_hidden(esk4_2(X2,X1),X1)|~r2_hidden(esk5_2(X2,X1),X3)|~r1_xboole_0(X3,X2)), inference(spm,[status(thm)],[c_0_9, c_0_19])).
% 0.13/0.36  cnf(c_0_24, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_20, c_0_10])).
% 0.13/0.36  cnf(c_0_25, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.13/0.36  cnf(c_0_26, plain, (X1=k3_tarski(X2)|r2_hidden(esk4_2(X2,X1),X1)|~r1_xboole_0(X2,X2)), inference(spm,[status(thm)],[c_0_23, c_0_19])).
% 0.13/0.36  cnf(c_0_27, plain, (r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.36  fof(c_0_28, negated_conjecture, ~(k3_tarski(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t2_zfmisc_1])).
% 0.13/0.36  cnf(c_0_29, plain, (X2=k3_tarski(X1)|~r2_hidden(esk4_2(X1,X2),X2)|~r2_hidden(esk4_2(X1,X2),X3)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_30, plain, (X1=k3_tarski(k1_xboole_0)|r2_hidden(esk4_2(k1_xboole_0,X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.36  fof(c_0_31, negated_conjecture, k3_tarski(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_28])).
% 0.13/0.36  cnf(c_0_32, plain, (X1=k3_tarski(k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_30])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.36  cnf(c_0_34, plain, (esk4_2(k1_xboole_0,k1_xboole_0)=k3_tarski(k1_xboole_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_33])).
% 0.13/0.36  cnf(c_0_35, plain, (r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_34]), c_0_25])]), c_0_33])).
% 0.13/0.36  cnf(c_0_36, plain, (~r2_hidden(k3_tarski(k1_xboole_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_35]), c_0_25])])).
% 0.13/0.36  cnf(c_0_37, plain, ($false), inference(sr,[status(thm)],[c_0_35, c_0_36]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 38
% 0.13/0.36  # Proof object clause steps            : 25
% 0.13/0.36  # Proof object formula steps           : 13
% 0.13/0.36  # Proof object conjectures             : 4
% 0.13/0.36  # Proof object clause conjectures      : 1
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 9
% 0.13/0.36  # Proof object initial formulas used   : 6
% 0.13/0.36  # Proof object generating inferences   : 15
% 0.13/0.36  # Proof object simplifying inferences  : 9
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 7
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 15
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 15
% 0.13/0.36  # Processed clauses                    : 60
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 1
% 0.13/0.36  # ...remaining for further processing  : 59
% 0.13/0.36  # Other redundant clauses eliminated   : 5
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 0
% 0.13/0.36  # Backward-rewritten                   : 2
% 0.13/0.36  # Generated clauses                    : 81
% 0.13/0.36  # ...of the previous two non-trivial   : 63
% 0.13/0.36  # Contextual simplify-reflections      : 1
% 0.13/0.36  # Paramodulations                      : 75
% 0.13/0.36  # Factorizations                       : 0
% 0.13/0.36  # Equation resolutions                 : 5
% 0.13/0.36  # Propositional unsat checks           : 0
% 0.13/0.36  #    Propositional check models        : 0
% 0.13/0.36  #    Propositional check unsatisfiable : 0
% 0.13/0.36  #    Propositional clauses             : 0
% 0.13/0.36  #    Propositional clauses after purity: 0
% 0.13/0.36  #    Propositional unsat core size     : 0
% 0.13/0.36  #    Propositional preprocessing time  : 0.000
% 0.13/0.36  #    Propositional encoding time       : 0.000
% 0.13/0.36  #    Propositional solver time         : 0.000
% 0.13/0.36  #    Success case prop preproc time    : 0.000
% 0.13/0.36  #    Success case prop encoding time   : 0.000
% 0.13/0.36  #    Success case prop solver time     : 0.000
% 0.13/0.36  # Current number of processed clauses  : 38
% 0.13/0.36  #    Positive orientable unit clauses  : 8
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 2
% 0.13/0.36  #    Non-unit-clauses                  : 28
% 0.13/0.36  # Current number of unprocessed clauses: 33
% 0.13/0.36  # ...number of literals in the above   : 95
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 18
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 93
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 82
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.36  # Unit Clause-clause subsumption calls : 2
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 4
% 0.13/0.36  # BW rewrite match successes           : 2
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 1988
% 0.13/0.36  
% 0.13/0.36  # -------------------------------------------------
% 0.13/0.36  # User time                : 0.021 s
% 0.13/0.36  # System time              : 0.006 s
% 0.13/0.36  # Total time               : 0.027 s
% 0.13/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
