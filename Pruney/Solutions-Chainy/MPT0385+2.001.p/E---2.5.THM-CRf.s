%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:00 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 384 expanded)
%              Number of clauses        :   29 ( 191 expanded)
%              Number of leaves         :    6 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  152 (2042 expanded)
%              Number of equality atoms :   58 ( 775 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t3_setfam_1,conjecture,(
    ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_setfam_1)).

fof(d1_setfam_1,axiom,(
    ! [X1,X2] :
      ( ( X1 != k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ! [X4] :
                  ( r2_hidden(X4,X1)
                 => r2_hidden(X3,X4) ) ) ) )
      & ( X1 = k1_xboole_0
       => ( X2 = k1_setfam_1(X1)
        <=> X2 = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(d4_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k3_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X3,X4)
              & r2_hidden(X4,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(t135_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X1,X2))
        | r1_tarski(X1,k2_zfmisc_1(X2,X1)) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(t2_zfmisc_1,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] : r1_tarski(k1_setfam_1(X1),k3_tarski(X1)) ),
    inference(assume_negation,[status(cth)],[t3_setfam_1])).

fof(c_0_7,plain,(
    ! [X24,X25,X26,X27,X28,X30,X33,X34,X35,X36] :
      ( ( ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X24)
        | r2_hidden(X26,X27)
        | X25 != k1_setfam_1(X24)
        | X24 = k1_xboole_0 )
      & ( r2_hidden(esk5_3(X24,X25,X28),X24)
        | r2_hidden(X28,X25)
        | X25 != k1_setfam_1(X24)
        | X24 = k1_xboole_0 )
      & ( ~ r2_hidden(X28,esk5_3(X24,X25,X28))
        | r2_hidden(X28,X25)
        | X25 != k1_setfam_1(X24)
        | X24 = k1_xboole_0 )
      & ( r2_hidden(esk7_2(X24,X30),X24)
        | ~ r2_hidden(esk6_2(X24,X30),X30)
        | X30 = k1_setfam_1(X24)
        | X24 = k1_xboole_0 )
      & ( ~ r2_hidden(esk6_2(X24,X30),esk7_2(X24,X30))
        | ~ r2_hidden(esk6_2(X24,X30),X30)
        | X30 = k1_setfam_1(X24)
        | X24 = k1_xboole_0 )
      & ( r2_hidden(esk6_2(X24,X30),X30)
        | ~ r2_hidden(X33,X24)
        | r2_hidden(esk6_2(X24,X30),X33)
        | X30 = k1_setfam_1(X24)
        | X24 = k1_xboole_0 )
      & ( X35 != k1_setfam_1(X34)
        | X35 = k1_xboole_0
        | X34 != k1_xboole_0 )
      & ( X36 != k1_xboole_0
        | X36 = k1_setfam_1(X34)
        | X34 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).

fof(c_0_8,negated_conjecture,(
    ~ r1_tarski(k1_setfam_1(esk8_0),k3_tarski(esk8_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

fof(c_0_9,plain,(
    ! [X5,X6,X7,X8,X9] :
      ( ( ~ r1_tarski(X5,X6)
        | ~ r2_hidden(X7,X5)
        | r2_hidden(X7,X6) )
      & ( r2_hidden(esk1_2(X8,X9),X8)
        | r1_tarski(X8,X9) )
      & ( ~ r2_hidden(esk1_2(X8,X9),X9)
        | r1_tarski(X8,X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,plain,(
    ! [X11,X12,X13,X15,X16,X17,X18,X20] :
      ( ( r2_hidden(X13,esk2_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( r2_hidden(esk2_3(X11,X12,X13),X11)
        | ~ r2_hidden(X13,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(X15,X16)
        | ~ r2_hidden(X16,X11)
        | r2_hidden(X15,X12)
        | X12 != k3_tarski(X11) )
      & ( ~ r2_hidden(esk3_2(X17,X18),X18)
        | ~ r2_hidden(esk3_2(X17,X18),X20)
        | ~ r2_hidden(X20,X17)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) )
      & ( r2_hidden(esk4_2(X17,X18),X17)
        | r2_hidden(esk3_2(X17,X18),X18)
        | X18 = k3_tarski(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X3)
    | X4 = k1_xboole_0
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X4)
    | X2 != k1_setfam_1(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ r1_tarski(k1_setfam_1(esk8_0),k3_tarski(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X3)
    | X4 != k3_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k1_setfam_1(X1))
    | ~ r2_hidden(X3,X1) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk1_2(k1_setfam_1(esk8_0),k3_tarski(esk8_0)),k1_setfam_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_17,plain,
    ( r2_hidden(esk5_3(X1,X2,X3),X1)
    | r2_hidden(X3,X2)
    | X1 = k1_xboole_0
    | X2 != k1_setfam_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_hidden(X1,k3_tarski(X2))
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(esk8_0),k3_tarski(esk8_0)),X1)
    | ~ r2_hidden(X1,esk8_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk5_3(X1,k1_setfam_1(X1),X2),X1)
    | r2_hidden(X2,k1_setfam_1(X1)) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(esk1_2(X1,k3_tarski(X2)),X3)
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(esk1_2(k1_setfam_1(esk8_0),k3_tarski(esk8_0)),esk5_3(esk8_0,k1_setfam_1(esk8_0),X1))
    | r2_hidden(X1,k1_setfam_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_24,plain,(
    ! [X22,X23] :
      ( ( ~ r1_tarski(X22,k2_zfmisc_1(X22,X23))
        | X22 = k1_xboole_0 )
      & ( ~ r1_tarski(X22,k2_zfmisc_1(X23,X22))
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).

cnf(c_0_25,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(X1,k1_setfam_1(esk8_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_12]),c_0_21])).

cnf(c_0_26,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X2,X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_27,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X2,esk8_0) ),
    inference(spm,[status(thm)],[c_0_15,c_0_25])).

cnf(c_0_28,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k2_zfmisc_1(X2,X1)),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_13])).

cnf(c_0_29,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r2_hidden(X1,esk1_2(esk8_0,k2_zfmisc_1(X2,esk8_0))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_31,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(esk1_2(esk8_0,k2_zfmisc_1(X3,esk8_0)),X2) ),
    inference(spm,[status(thm)],[c_0_22,c_0_29])).

cnf(c_0_32,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk1_2(X1,k2_zfmisc_1(X1,X2)),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_13])).

cnf(c_0_33,negated_conjecture,
    ( esk8_0 = k1_xboole_0
    | r1_tarski(X1,k3_tarski(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | X1 != k1_setfam_1(X2)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_35,negated_conjecture,
    ( esk8_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_12,c_0_33])).

cnf(c_0_36,plain,
    ( k1_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).

cnf(c_0_37,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16,c_0_35]),c_0_36]),c_0_35]),c_0_37]),c_0_35]),c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12,c_0_35]),c_0_36]),c_0_35]),c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_38]),c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 17:36:56 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  # Version: 2.5pre002
% 0.13/0.32  # No SInE strategy applied
% 0.13/0.32  # Trying AutoSched0 for 299 seconds
% 0.13/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S080I
% 0.13/0.36  # and selection function SelectCQIArNXTEqFirst.
% 0.13/0.36  #
% 0.13/0.36  # Preprocessing time       : 0.028 s
% 0.13/0.36  # Presaturation interreduction done
% 0.13/0.36  
% 0.13/0.36  # Proof found!
% 0.13/0.36  # SZS status Theorem
% 0.13/0.36  # SZS output start CNFRefutation
% 0.13/0.36  fof(t3_setfam_1, conjecture, ![X1]:r1_tarski(k1_setfam_1(X1),k3_tarski(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_setfam_1)).
% 0.13/0.36  fof(d1_setfam_1, axiom, ![X1, X2]:((X1!=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>![X4]:(r2_hidden(X4,X1)=>r2_hidden(X3,X4)))))&(X1=k1_xboole_0=>(X2=k1_setfam_1(X1)<=>X2=k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 0.13/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.13/0.36  fof(d4_tarski, axiom, ![X1, X2]:(X2=k3_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X3,X4)&r2_hidden(X4,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 0.13/0.36  fof(t135_zfmisc_1, axiom, ![X1, X2]:((r1_tarski(X1,k2_zfmisc_1(X1,X2))|r1_tarski(X1,k2_zfmisc_1(X2,X1)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 0.13/0.36  fof(t2_zfmisc_1, axiom, k3_tarski(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 0.13/0.36  fof(c_0_6, negated_conjecture, ~(![X1]:r1_tarski(k1_setfam_1(X1),k3_tarski(X1))), inference(assume_negation,[status(cth)],[t3_setfam_1])).
% 0.13/0.36  fof(c_0_7, plain, ![X24, X25, X26, X27, X28, X30, X33, X34, X35, X36]:((((~r2_hidden(X26,X25)|(~r2_hidden(X27,X24)|r2_hidden(X26,X27))|X25!=k1_setfam_1(X24)|X24=k1_xboole_0)&((r2_hidden(esk5_3(X24,X25,X28),X24)|r2_hidden(X28,X25)|X25!=k1_setfam_1(X24)|X24=k1_xboole_0)&(~r2_hidden(X28,esk5_3(X24,X25,X28))|r2_hidden(X28,X25)|X25!=k1_setfam_1(X24)|X24=k1_xboole_0)))&(((r2_hidden(esk7_2(X24,X30),X24)|~r2_hidden(esk6_2(X24,X30),X30)|X30=k1_setfam_1(X24)|X24=k1_xboole_0)&(~r2_hidden(esk6_2(X24,X30),esk7_2(X24,X30))|~r2_hidden(esk6_2(X24,X30),X30)|X30=k1_setfam_1(X24)|X24=k1_xboole_0))&(r2_hidden(esk6_2(X24,X30),X30)|(~r2_hidden(X33,X24)|r2_hidden(esk6_2(X24,X30),X33))|X30=k1_setfam_1(X24)|X24=k1_xboole_0)))&((X35!=k1_setfam_1(X34)|X35=k1_xboole_0|X34!=k1_xboole_0)&(X36!=k1_xboole_0|X36=k1_setfam_1(X34)|X34!=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_setfam_1])])])])])])).
% 0.13/0.36  fof(c_0_8, negated_conjecture, ~r1_tarski(k1_setfam_1(esk8_0),k3_tarski(esk8_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.13/0.36  fof(c_0_9, plain, ![X5, X6, X7, X8, X9]:((~r1_tarski(X5,X6)|(~r2_hidden(X7,X5)|r2_hidden(X7,X6)))&((r2_hidden(esk1_2(X8,X9),X8)|r1_tarski(X8,X9))&(~r2_hidden(esk1_2(X8,X9),X9)|r1_tarski(X8,X9)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.13/0.36  fof(c_0_10, plain, ![X11, X12, X13, X15, X16, X17, X18, X20]:((((r2_hidden(X13,esk2_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k3_tarski(X11))&(r2_hidden(esk2_3(X11,X12,X13),X11)|~r2_hidden(X13,X12)|X12!=k3_tarski(X11)))&(~r2_hidden(X15,X16)|~r2_hidden(X16,X11)|r2_hidden(X15,X12)|X12!=k3_tarski(X11)))&((~r2_hidden(esk3_2(X17,X18),X18)|(~r2_hidden(esk3_2(X17,X18),X20)|~r2_hidden(X20,X17))|X18=k3_tarski(X17))&((r2_hidden(esk3_2(X17,X18),esk4_2(X17,X18))|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))&(r2_hidden(esk4_2(X17,X18),X17)|r2_hidden(esk3_2(X17,X18),X18)|X18=k3_tarski(X17))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tarski])])])])])])).
% 0.13/0.36  cnf(c_0_11, plain, (r2_hidden(X1,X3)|X4=k1_xboole_0|~r2_hidden(X1,X2)|~r2_hidden(X3,X4)|X2!=k1_setfam_1(X4)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.36  cnf(c_0_12, negated_conjecture, (~r1_tarski(k1_setfam_1(esk8_0),k3_tarski(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.36  cnf(c_0_13, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_14, plain, (r2_hidden(X1,X4)|~r2_hidden(X1,X2)|~r2_hidden(X2,X3)|X4!=k3_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.13/0.36  cnf(c_0_15, plain, (X1=k1_xboole_0|r2_hidden(X2,X3)|~r2_hidden(X2,k1_setfam_1(X1))|~r2_hidden(X3,X1)), inference(er,[status(thm)],[c_0_11])).
% 0.13/0.36  cnf(c_0_16, negated_conjecture, (r2_hidden(esk1_2(k1_setfam_1(esk8_0),k3_tarski(esk8_0)),k1_setfam_1(esk8_0))), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.13/0.36  cnf(c_0_17, plain, (r2_hidden(esk5_3(X1,X2,X3),X1)|r2_hidden(X3,X2)|X1=k1_xboole_0|X2!=k1_setfam_1(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.36  cnf(c_0_18, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.36  cnf(c_0_19, plain, (r2_hidden(X1,k3_tarski(X2))|~r2_hidden(X3,X2)|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_14])).
% 0.13/0.36  cnf(c_0_20, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(esk8_0),k3_tarski(esk8_0)),X1)|~r2_hidden(X1,esk8_0)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.13/0.36  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk5_3(X1,k1_setfam_1(X1),X2),X1)|r2_hidden(X2,k1_setfam_1(X1))), inference(er,[status(thm)],[c_0_17])).
% 0.13/0.36  cnf(c_0_22, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(esk1_2(X1,k3_tarski(X2)),X3)|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.13/0.36  cnf(c_0_23, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(esk1_2(k1_setfam_1(esk8_0),k3_tarski(esk8_0)),esk5_3(esk8_0,k1_setfam_1(esk8_0),X1))|r2_hidden(X1,k1_setfam_1(esk8_0))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.36  fof(c_0_24, plain, ![X22, X23]:((~r1_tarski(X22,k2_zfmisc_1(X22,X23))|X22=k1_xboole_0)&(~r1_tarski(X22,k2_zfmisc_1(X23,X22))|X22=k1_xboole_0)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t135_zfmisc_1])])])).
% 0.13/0.36  cnf(c_0_25, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(X1,k1_setfam_1(esk8_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_12]), c_0_21])).
% 0.13/0.36  cnf(c_0_26, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X2,X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.36  cnf(c_0_27, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(X1,X2)|~r2_hidden(X2,esk8_0)), inference(spm,[status(thm)],[c_0_15, c_0_25])).
% 0.13/0.36  cnf(c_0_28, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k2_zfmisc_1(X2,X1)),X1)), inference(spm,[status(thm)],[c_0_26, c_0_13])).
% 0.13/0.36  cnf(c_0_29, negated_conjecture, (esk8_0=k1_xboole_0|r2_hidden(X1,esk1_2(esk8_0,k2_zfmisc_1(X2,esk8_0)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.36  cnf(c_0_30, plain, (X1=k1_xboole_0|~r1_tarski(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.36  cnf(c_0_31, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(X1,k3_tarski(X2))|~r2_hidden(esk1_2(esk8_0,k2_zfmisc_1(X3,esk8_0)),X2)), inference(spm,[status(thm)],[c_0_22, c_0_29])).
% 0.13/0.36  cnf(c_0_32, plain, (X1=k1_xboole_0|r2_hidden(esk1_2(X1,k2_zfmisc_1(X1,X2)),X1)), inference(spm,[status(thm)],[c_0_30, c_0_13])).
% 0.13/0.36  cnf(c_0_33, negated_conjecture, (esk8_0=k1_xboole_0|r1_tarski(X1,k3_tarski(esk8_0))), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.13/0.36  cnf(c_0_34, plain, (X1=k1_xboole_0|X1!=k1_setfam_1(X2)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.36  cnf(c_0_35, negated_conjecture, (esk8_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_12, c_0_33])).
% 0.13/0.36  cnf(c_0_36, plain, (k1_setfam_1(k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_34])])).
% 0.13/0.36  cnf(c_0_37, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t2_zfmisc_1])).
% 0.13/0.36  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_2(k1_xboole_0,k1_xboole_0),k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_16, c_0_35]), c_0_36]), c_0_35]), c_0_37]), c_0_35]), c_0_36])).
% 0.13/0.36  cnf(c_0_39, negated_conjecture, (~r1_tarski(k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_12, c_0_35]), c_0_36]), c_0_35]), c_0_37])).
% 0.13/0.36  cnf(c_0_40, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_38]), c_0_39]), ['proof']).
% 0.13/0.36  # SZS output end CNFRefutation
% 0.13/0.36  # Proof object total steps             : 41
% 0.13/0.36  # Proof object clause steps            : 29
% 0.13/0.36  # Proof object formula steps           : 12
% 0.13/0.36  # Proof object conjectures             : 16
% 0.13/0.36  # Proof object clause conjectures      : 13
% 0.13/0.36  # Proof object formula conjectures     : 3
% 0.13/0.36  # Proof object initial clauses used    : 10
% 0.13/0.36  # Proof object initial formulas used   : 6
% 0.13/0.36  # Proof object generating inferences   : 13
% 0.13/0.36  # Proof object simplifying inferences  : 18
% 0.13/0.36  # Training examples: 0 positive, 0 negative
% 0.13/0.36  # Parsed axioms                        : 6
% 0.13/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.36  # Initial clauses                      : 21
% 0.13/0.36  # Removed in clause preprocessing      : 0
% 0.13/0.36  # Initial clauses in saturation        : 21
% 0.13/0.36  # Processed clauses                    : 139
% 0.13/0.36  # ...of these trivial                  : 0
% 0.13/0.36  # ...subsumed                          : 38
% 0.13/0.36  # ...remaining for further processing  : 101
% 0.13/0.36  # Other redundant clauses eliminated   : 10
% 0.13/0.36  # Clauses deleted for lack of memory   : 0
% 0.13/0.36  # Backward-subsumed                    : 8
% 0.13/0.36  # Backward-rewritten                   : 31
% 0.13/0.36  # Generated clauses                    : 427
% 0.13/0.36  # ...of the previous two non-trivial   : 426
% 0.13/0.36  # Contextual simplify-reflections      : 1
% 0.13/0.36  # Paramodulations                      : 417
% 0.13/0.36  # Factorizations                       : 2
% 0.13/0.36  # Equation resolutions                 : 10
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
% 0.13/0.36  # Current number of processed clauses  : 34
% 0.13/0.36  #    Positive orientable unit clauses  : 4
% 0.13/0.36  #    Positive unorientable unit clauses: 0
% 0.13/0.36  #    Negative unit clauses             : 2
% 0.13/0.36  #    Non-unit-clauses                  : 28
% 0.13/0.36  # Current number of unprocessed clauses: 312
% 0.13/0.36  # ...number of literals in the above   : 1284
% 0.13/0.36  # Current number of archived formulas  : 0
% 0.13/0.36  # Current number of archived clauses   : 59
% 0.13/0.36  # Clause-clause subsumption calls (NU) : 460
% 0.13/0.36  # Rec. Clause-clause subsumption calls : 313
% 0.13/0.36  # Non-unit clause-clause subsumptions  : 47
% 0.13/0.36  # Unit Clause-clause subsumption calls : 17
% 0.13/0.36  # Rewrite failures with RHS unbound    : 0
% 0.13/0.36  # BW rewrite match attempts            : 1
% 0.13/0.36  # BW rewrite match successes           : 1
% 0.13/0.36  # Condensation attempts                : 0
% 0.13/0.36  # Condensation successes               : 0
% 0.13/0.36  # Termbank termtop insertions          : 7563
% 0.13/0.37  
% 0.13/0.37  # -------------------------------------------------
% 0.13/0.37  # User time                : 0.041 s
% 0.13/0.37  # System time              : 0.002 s
% 0.13/0.37  # Total time               : 0.043 s
% 0.13/0.37  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
