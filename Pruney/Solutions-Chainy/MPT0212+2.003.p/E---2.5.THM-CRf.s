%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:36:53 EST 2020

% Result     : Theorem 0.11s
% Output     : CNFRefutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   39 (  63 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 182 expanded)
%              Number of equality atoms :   74 ( 123 expanded)
%              Maximal formula depth    :   22 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(t3_xboole_1,axiom,(
    ! [X1] :
      ( r1_tarski(X1,k1_xboole_0)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(d1_enumset1,axiom,(
    ! [X1,X2,X3,X4] :
      ( X4 = k1_enumset1(X1,X2,X3)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X5 != X1
              & X5 != X2
              & X5 != X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(t71_enumset1,axiom,(
    ! [X1,X2,X3] : k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(t1_zfmisc_1,conjecture,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t70_enumset1,axiom,(
    ! [X1,X2] : k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(c_0_8,plain,(
    ! [X25,X26,X27,X28,X29,X30] :
      ( ( ~ r2_hidden(X27,X26)
        | r1_tarski(X27,X25)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r1_tarski(X28,X25)
        | r2_hidden(X28,X26)
        | X26 != k1_zfmisc_1(X25) )
      & ( ~ r2_hidden(esk2_2(X29,X30),X30)
        | ~ r1_tarski(esk2_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) )
      & ( r2_hidden(esk2_2(X29,X30),X30)
        | r1_tarski(esk2_2(X29,X30),X29)
        | X30 = k1_zfmisc_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

fof(c_0_9,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k1_xboole_0)
      | X7 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).

cnf(c_0_10,plain,
    ( r1_tarski(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_zfmisc_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X8,X9,X10,X11,X12,X13,X14,X15,X16,X17] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X8
        | X12 = X9
        | X12 = X10
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( X13 != X8
        | r2_hidden(X13,X11)
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( X13 != X9
        | r2_hidden(X13,X11)
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_enumset1(X8,X9,X10) )
      & ( esk1_4(X14,X15,X16,X17) != X14
        | ~ r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | X17 = k1_enumset1(X14,X15,X16) )
      & ( esk1_4(X14,X15,X16,X17) != X15
        | ~ r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | X17 = k1_enumset1(X14,X15,X16) )
      & ( esk1_4(X14,X15,X16,X17) != X16
        | ~ r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | X17 = k1_enumset1(X14,X15,X16) )
      & ( r2_hidden(esk1_4(X14,X15,X16,X17),X17)
        | esk1_4(X14,X15,X16,X17) = X14
        | esk1_4(X14,X15,X16,X17) = X15
        | esk1_4(X14,X15,X16,X17) = X16
        | X17 = k1_enumset1(X14,X15,X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).

fof(c_0_12,plain,(
    ! [X22,X23,X24] : k2_enumset1(X22,X22,X23,X24) = k1_enumset1(X22,X23,X24) ),
    inference(variable_rename,[status(thm)],[t71_enumset1])).

cnf(c_0_13,plain,
    ( X1 = k1_xboole_0
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(X1,k1_zfmisc_1(X2)) ),
    inference(er,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_4(X1,X2,X3,X4),X4)
    | esk1_4(X1,X2,X3,X4) = X1
    | esk1_4(X1,X2,X3,X4) = X2
    | esk1_4(X1,X2,X3,X4) = X3
    | X4 = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( k2_enumset1(X1,X1,X2,X3) = k1_enumset1(X1,X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( X1 = k1_xboole_0
    | ~ r2_hidden(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) = X3
    | esk1_4(X1,X2,X3,X4) = X2
    | esk1_4(X1,X2,X3,X4) = X1
    | r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_19,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(assume_negation,[status(cth)],[t1_zfmisc_1])).

cnf(c_0_20,plain,
    ( esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0)) = X1
    | esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0)) = X2
    | esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0)) = X3
    | k1_zfmisc_1(k1_xboole_0) = k2_enumset1(X1,X1,X2,X3) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

fof(c_0_21,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(fof_simplification,[status(thm)],[c_0_19])).

fof(c_0_22,plain,(
    ! [X19] : k2_tarski(X19,X19) = k1_tarski(X19) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_23,plain,(
    ! [X20,X21] : k1_enumset1(X20,X20,X21) = k2_tarski(X20,X21) ),
    inference(variable_rename,[status(thm)],[t70_enumset1])).

cnf(c_0_24,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,X1,X2)
    | esk1_4(k1_xboole_0,X1,X2,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | esk1_4(k1_xboole_0,X1,X2,k1_zfmisc_1(k1_xboole_0)) = X2
    | esk1_4(k1_xboole_0,X1,X2,k1_zfmisc_1(k1_xboole_0)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_20])])).

cnf(c_0_25,negated_conjecture,
    ( k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( k1_enumset1(X1,X1,X2) = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_29,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

cnf(c_0_30,plain,
    ( X4 = k1_enumset1(X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_31,plain,
    ( esk1_4(k1_xboole_0,X1,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,X1,k1_xboole_0)
    | esk1_4(k1_xboole_0,X1,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = X1 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).

cnf(c_0_32,negated_conjecture,
    ( k1_zfmisc_1(k1_xboole_0) != k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_16])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_35,plain,
    ( X4 = k2_enumset1(X1,X1,X2,X3)
    | esk1_4(X1,X2,X3,X4) != X3
    | ~ r2_hidden(esk1_4(X1,X2,X3,X4),X4) ),
    inference(rw,[status(thm)],[c_0_30,c_0_16])).

cnf(c_0_36,plain,
    ( esk1_4(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_31])]),c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_38,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])]),c_0_32]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:25:49 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.11/0.36  # AutoSched0-Mode selected heuristic G_E___107_B42_F1_PI_SE_Q4_CS_SP_PS_S0YI
% 0.11/0.36  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.11/0.36  #
% 0.11/0.36  # Preprocessing time       : 0.026 s
% 0.11/0.36  # Presaturation interreduction done
% 0.11/0.36  
% 0.11/0.36  # Proof found!
% 0.11/0.36  # SZS status Theorem
% 0.11/0.36  # SZS output start CNFRefutation
% 0.11/0.36  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.11/0.36  fof(t3_xboole_1, axiom, ![X1]:(r1_tarski(X1,k1_xboole_0)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 0.11/0.36  fof(d1_enumset1, axiom, ![X1, X2, X3, X4]:(X4=k1_enumset1(X1,X2,X3)<=>![X5]:(r2_hidden(X5,X4)<=>~(((X5!=X1&X5!=X2)&X5!=X3)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 0.11/0.36  fof(t71_enumset1, axiom, ![X1, X2, X3]:k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 0.11/0.36  fof(t1_zfmisc_1, conjecture, k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 0.11/0.36  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.11/0.36  fof(t70_enumset1, axiom, ![X1, X2]:k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 0.11/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.11/0.36  fof(c_0_8, plain, ![X25, X26, X27, X28, X29, X30]:(((~r2_hidden(X27,X26)|r1_tarski(X27,X25)|X26!=k1_zfmisc_1(X25))&(~r1_tarski(X28,X25)|r2_hidden(X28,X26)|X26!=k1_zfmisc_1(X25)))&((~r2_hidden(esk2_2(X29,X30),X30)|~r1_tarski(esk2_2(X29,X30),X29)|X30=k1_zfmisc_1(X29))&(r2_hidden(esk2_2(X29,X30),X30)|r1_tarski(esk2_2(X29,X30),X29)|X30=k1_zfmisc_1(X29)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.11/0.36  fof(c_0_9, plain, ![X7]:(~r1_tarski(X7,k1_xboole_0)|X7=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_xboole_1])])).
% 0.11/0.36  cnf(c_0_10, plain, (r1_tarski(X1,X3)|~r2_hidden(X1,X2)|X2!=k1_zfmisc_1(X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.36  fof(c_0_11, plain, ![X8, X9, X10, X11, X12, X13, X14, X15, X16, X17]:(((~r2_hidden(X12,X11)|(X12=X8|X12=X9|X12=X10)|X11!=k1_enumset1(X8,X9,X10))&(((X13!=X8|r2_hidden(X13,X11)|X11!=k1_enumset1(X8,X9,X10))&(X13!=X9|r2_hidden(X13,X11)|X11!=k1_enumset1(X8,X9,X10)))&(X13!=X10|r2_hidden(X13,X11)|X11!=k1_enumset1(X8,X9,X10))))&((((esk1_4(X14,X15,X16,X17)!=X14|~r2_hidden(esk1_4(X14,X15,X16,X17),X17)|X17=k1_enumset1(X14,X15,X16))&(esk1_4(X14,X15,X16,X17)!=X15|~r2_hidden(esk1_4(X14,X15,X16,X17),X17)|X17=k1_enumset1(X14,X15,X16)))&(esk1_4(X14,X15,X16,X17)!=X16|~r2_hidden(esk1_4(X14,X15,X16,X17),X17)|X17=k1_enumset1(X14,X15,X16)))&(r2_hidden(esk1_4(X14,X15,X16,X17),X17)|(esk1_4(X14,X15,X16,X17)=X14|esk1_4(X14,X15,X16,X17)=X15|esk1_4(X14,X15,X16,X17)=X16)|X17=k1_enumset1(X14,X15,X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_enumset1])])])])])])).
% 0.11/0.36  fof(c_0_12, plain, ![X22, X23, X24]:k2_enumset1(X22,X22,X23,X24)=k1_enumset1(X22,X23,X24), inference(variable_rename,[status(thm)],[t71_enumset1])).
% 0.11/0.36  cnf(c_0_13, plain, (X1=k1_xboole_0|~r1_tarski(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.11/0.36  cnf(c_0_14, plain, (r1_tarski(X1,X2)|~r2_hidden(X1,k1_zfmisc_1(X2))), inference(er,[status(thm)],[c_0_10])).
% 0.11/0.36  cnf(c_0_15, plain, (r2_hidden(esk1_4(X1,X2,X3,X4),X4)|esk1_4(X1,X2,X3,X4)=X1|esk1_4(X1,X2,X3,X4)=X2|esk1_4(X1,X2,X3,X4)=X3|X4=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_16, plain, (k2_enumset1(X1,X1,X2,X3)=k1_enumset1(X1,X2,X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.11/0.36  cnf(c_0_17, plain, (X1=k1_xboole_0|~r2_hidden(X1,k1_zfmisc_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.11/0.36  cnf(c_0_18, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)=X3|esk1_4(X1,X2,X3,X4)=X2|esk1_4(X1,X2,X3,X4)=X1|r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 0.11/0.36  fof(c_0_19, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(assume_negation,[status(cth)],[t1_zfmisc_1])).
% 0.11/0.36  cnf(c_0_20, plain, (esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0))=X1|esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0))=X2|esk1_4(X1,X2,X3,k1_zfmisc_1(k1_xboole_0))=X3|k1_zfmisc_1(k1_xboole_0)=k2_enumset1(X1,X1,X2,X3)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.11/0.36  fof(c_0_21, negated_conjecture, k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0), inference(fof_simplification,[status(thm)],[c_0_19])).
% 0.11/0.36  fof(c_0_22, plain, ![X19]:k2_tarski(X19,X19)=k1_tarski(X19), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.11/0.36  fof(c_0_23, plain, ![X20, X21]:k1_enumset1(X20,X20,X21)=k2_tarski(X20,X21), inference(variable_rename,[status(thm)],[t70_enumset1])).
% 0.11/0.36  cnf(c_0_24, plain, (k1_zfmisc_1(k1_xboole_0)=k2_enumset1(k1_xboole_0,k1_xboole_0,X1,X2)|esk1_4(k1_xboole_0,X1,X2,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|esk1_4(k1_xboole_0,X1,X2,k1_zfmisc_1(k1_xboole_0))=X2|esk1_4(k1_xboole_0,X1,X2,k1_zfmisc_1(k1_xboole_0))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_20])])).
% 0.11/0.36  cnf(c_0_25, negated_conjecture, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.11/0.36  cnf(c_0_26, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.11/0.36  cnf(c_0_27, plain, (k1_enumset1(X1,X1,X2)=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.11/0.36  cnf(c_0_28, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.11/0.36  fof(c_0_29, plain, ![X6]:r1_tarski(k1_xboole_0,X6), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.11/0.36  cnf(c_0_30, plain, (X4=k1_enumset1(X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.11/0.36  cnf(c_0_31, plain, (esk1_4(k1_xboole_0,X1,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0|k1_zfmisc_1(k1_xboole_0)=k2_enumset1(k1_xboole_0,k1_xboole_0,X1,k1_xboole_0)|esk1_4(k1_xboole_0,X1,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))=X1), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_24])])).
% 0.11/0.36  cnf(c_0_32, negated_conjecture, (k1_zfmisc_1(k1_xboole_0)!=k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_16])).
% 0.11/0.36  cnf(c_0_33, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_28])).
% 0.11/0.36  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.11/0.36  cnf(c_0_35, plain, (X4=k2_enumset1(X1,X1,X2,X3)|esk1_4(X1,X2,X3,X4)!=X3|~r2_hidden(esk1_4(X1,X2,X3,X4),X4)), inference(rw,[status(thm)],[c_0_30, c_0_16])).
% 0.11/0.36  cnf(c_0_36, plain, (esk1_4(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_zfmisc_1(k1_xboole_0))=k1_xboole_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_31])]), c_0_32])).
% 0.11/0.36  cnf(c_0_37, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.11/0.36  cnf(c_0_38, plain, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37])]), c_0_32]), ['proof']).
% 0.11/0.36  # SZS output end CNFRefutation
% 0.11/0.36  # Proof object total steps             : 39
% 0.11/0.36  # Proof object clause steps            : 22
% 0.11/0.36  # Proof object formula steps           : 17
% 0.11/0.36  # Proof object conjectures             : 5
% 0.11/0.36  # Proof object clause conjectures      : 2
% 0.11/0.36  # Proof object formula conjectures     : 3
% 0.11/0.36  # Proof object initial clauses used    : 10
% 0.11/0.36  # Proof object initial formulas used   : 8
% 0.11/0.36  # Proof object generating inferences   : 7
% 0.11/0.36  # Proof object simplifying inferences  : 14
% 0.11/0.36  # Training examples: 0 positive, 0 negative
% 0.11/0.36  # Parsed axioms                        : 8
% 0.11/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.11/0.36  # Initial clauses                      : 18
% 0.11/0.36  # Removed in clause preprocessing      : 3
% 0.11/0.36  # Initial clauses in saturation        : 15
% 0.11/0.36  # Processed clauses                    : 52
% 0.11/0.36  # ...of these trivial                  : 0
% 0.11/0.36  # ...subsumed                          : 2
% 0.11/0.36  # ...remaining for further processing  : 50
% 0.11/0.36  # Other redundant clauses eliminated   : 92
% 0.11/0.36  # Clauses deleted for lack of memory   : 0
% 0.11/0.36  # Backward-subsumed                    : 0
% 0.11/0.36  # Backward-rewritten                   : 0
% 0.11/0.36  # Generated clauses                    : 223
% 0.11/0.36  # ...of the previous two non-trivial   : 125
% 0.11/0.36  # Contextual simplify-reflections      : 0
% 0.11/0.36  # Paramodulations                      : 82
% 0.11/0.36  # Factorizations                       : 52
% 0.11/0.36  # Equation resolutions                 : 92
% 0.11/0.36  # Propositional unsat checks           : 0
% 0.11/0.36  #    Propositional check models        : 0
% 0.11/0.36  #    Propositional check unsatisfiable : 0
% 0.11/0.36  #    Propositional clauses             : 0
% 0.11/0.36  #    Propositional clauses after purity: 0
% 0.11/0.36  #    Propositional unsat core size     : 0
% 0.11/0.36  #    Propositional preprocessing time  : 0.000
% 0.11/0.36  #    Propositional encoding time       : 0.000
% 0.11/0.36  #    Propositional solver time         : 0.000
% 0.11/0.36  #    Success case prop preproc time    : 0.000
% 0.11/0.36  #    Success case prop encoding time   : 0.000
% 0.11/0.36  #    Success case prop solver time     : 0.000
% 0.11/0.36  # Current number of processed clauses  : 29
% 0.11/0.36  #    Positive orientable unit clauses  : 6
% 0.11/0.36  #    Positive unorientable unit clauses: 0
% 0.11/0.36  #    Negative unit clauses             : 1
% 0.11/0.36  #    Non-unit-clauses                  : 22
% 0.11/0.36  # Current number of unprocessed clauses: 103
% 0.11/0.36  # ...number of literals in the above   : 522
% 0.11/0.36  # Current number of archived formulas  : 0
% 0.11/0.36  # Current number of archived clauses   : 18
% 0.11/0.36  # Clause-clause subsumption calls (NU) : 42
% 0.11/0.36  # Rec. Clause-clause subsumption calls : 29
% 0.11/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.11/0.36  # Unit Clause-clause subsumption calls : 9
% 0.11/0.36  # Rewrite failures with RHS unbound    : 0
% 0.11/0.36  # BW rewrite match attempts            : 6
% 0.11/0.36  # BW rewrite match successes           : 0
% 0.11/0.36  # Condensation attempts                : 0
% 0.11/0.36  # Condensation successes               : 0
% 0.11/0.36  # Termbank termtop insertions          : 4376
% 0.11/0.36  
% 0.11/0.36  # -------------------------------------------------
% 0.11/0.36  # User time                : 0.031 s
% 0.11/0.36  # System time              : 0.003 s
% 0.11/0.36  # Total time               : 0.034 s
% 0.11/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
