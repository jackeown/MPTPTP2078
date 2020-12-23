%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:43:38 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 170 expanded)
%              Number of clauses        :   39 (  81 expanded)
%              Number of leaves         :    7 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  129 ( 490 expanded)
%              Number of equality atoms :   37 ( 143 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t124_zfmisc_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X3,X4) )
     => k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X3)) = k2_zfmisc_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(d5_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k4_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & ~ r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(t123_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] : k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ( ( r1_tarski(X1,X2)
          & r1_tarski(X3,X4) )
       => k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X3)) = k2_zfmisc_1(X1,X3) ) ),
    inference(assume_negation,[status(cth)],[t124_zfmisc_1])).

fof(c_0_8,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k4_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k4_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k4_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).

fof(c_0_9,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_10,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0)
    & r1_tarski(esk5_0,esk6_0)
    & k3_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk4_0,esk5_0)) != k2_zfmisc_1(esk3_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k4_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X4 != k4_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( r1_tarski(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ( r1_tarski(X22,X23)
        | X22 != X23 )
      & ( r1_tarski(X23,X22)
        | X22 != X23 )
      & ( ~ r1_tarski(X22,X23)
        | ~ r1_tarski(X23,X22)
        | X22 = X23 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_20,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)
    | r1_tarski(k4_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_22,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_23,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,X27)) = k3_xboole_0(X26,X27) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k4_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,k4_xboole_0(X2,X3))
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),esk6_0)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_15])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,esk4_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_12,c_0_18])).

fof(c_0_28,plain,(
    ! [X28,X29,X30,X31] : k2_zfmisc_1(k3_xboole_0(X28,X29),k3_xboole_0(X30,X31)) = k3_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)) ),
    inference(variable_rename,[status(thm)],[t123_zfmisc_1])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r1_tarski(k4_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_32,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,k4_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,X1),k4_xboole_0(esk6_0,X2))
    | r2_hidden(esk1_2(esk5_0,X1),X2)
    | r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),esk4_0)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( k3_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk4_0,esk5_0)) != k2_zfmisc_1(esk3_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4)) = k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( k4_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,k4_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31,c_0_32]),c_0_32])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_15])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk1_2(esk5_0,k4_xboole_0(esk6_0,X1)),X1)
    | r1_tarski(esk5_0,k4_xboole_0(esk6_0,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,X1),k4_xboole_0(esk4_0,X2))
    | r2_hidden(esk1_2(esk3_0,X1),X2)
    | r1_tarski(esk3_0,X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk4_0,esk5_0))) != k2_zfmisc_1(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_36,c_0_32])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4))) = k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37,c_0_32]),c_0_32]),c_0_32])).

cnf(c_0_45,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = X2
    | ~ r1_tarski(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_46,negated_conjecture,
    ( r1_tarski(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk1_2(esk3_0,k4_xboole_0(esk4_0,X1)),X1)
    | r1_tarski(esk3_0,k4_xboole_0(esk4_0,X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))) != k2_zfmisc_1(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44]),c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)) = esk5_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( r1_tarski(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(X1,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_40,c_0_47])).

cnf(c_0_51,negated_conjecture,
    ( k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0) != k2_zfmisc_1(esk3_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_52,negated_conjecture,
    ( k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)) = esk3_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_50]),c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S078N
% 0.19/0.39  # and selection function SelectCQIArNpEqFirst.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.028 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t124_zfmisc_1, conjecture, ![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X3))=k2_zfmisc_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 0.19/0.39  fof(d5_xboole_0, axiom, ![X1, X2, X3]:(X3=k4_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&~(r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 0.19/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(commutativity_k3_xboole_0, axiom, ![X1, X2]:k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 0.19/0.39  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.19/0.39  fof(t123_zfmisc_1, axiom, ![X1, X2, X3, X4]:k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 0.19/0.39  fof(c_0_7, negated_conjecture, ~(![X1, X2, X3, X4]:((r1_tarski(X1,X2)&r1_tarski(X3,X4))=>k3_xboole_0(k2_zfmisc_1(X1,X4),k2_zfmisc_1(X2,X3))=k2_zfmisc_1(X1,X3))), inference(assume_negation,[status(cth)],[t124_zfmisc_1])).
% 0.19/0.39  fof(c_0_8, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14))&(~r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k4_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k4_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k4_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))&(~r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k4_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_xboole_0])])])])])])])).
% 0.19/0.39  fof(c_0_9, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.39  fof(c_0_10, negated_conjecture, ((r1_tarski(esk3_0,esk4_0)&r1_tarski(esk5_0,esk6_0))&k3_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk4_0,esk5_0))!=k2_zfmisc_1(esk3_0,esk5_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).
% 0.19/0.39  cnf(c_0_11, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X2,X4)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_12, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_13, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_14, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k4_xboole_0(X2,X3))), inference(er,[status(thm)],[c_0_11])).
% 0.19/0.39  cnf(c_0_15, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_16, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X4!=k4_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_17, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_12, c_0_13])).
% 0.19/0.39  cnf(c_0_18, negated_conjecture, (r1_tarski(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  fof(c_0_19, plain, ![X22, X23]:(((r1_tarski(X22,X23)|X22!=X23)&(r1_tarski(X23,X22)|X22!=X23))&(~r1_tarski(X22,X23)|~r1_tarski(X23,X22)|X22=X23)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  cnf(c_0_20, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.19/0.39  cnf(c_0_21, plain, (r2_hidden(esk1_2(k4_xboole_0(X1,X2),X3),X1)|r1_tarski(k4_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.19/0.39  fof(c_0_22, plain, ![X5, X6]:k3_xboole_0(X5,X6)=k3_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).
% 0.19/0.39  fof(c_0_23, plain, ![X26, X27]:k4_xboole_0(X26,k4_xboole_0(X26,X27))=k3_xboole_0(X26,X27), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.19/0.39  cnf(c_0_24, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|X3!=k4_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.19/0.39  cnf(c_0_25, plain, (r2_hidden(X1,k4_xboole_0(X2,X3))|r2_hidden(X1,X3)|~r2_hidden(X1,X2)), inference(er,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_26, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),esk6_0)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_17, c_0_15])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,esk4_0)|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_12, c_0_18])).
% 0.19/0.39  fof(c_0_28, plain, ![X28, X29, X30, X31]:k2_zfmisc_1(k3_xboole_0(X28,X29),k3_xboole_0(X30,X31))=k3_xboole_0(k2_zfmisc_1(X28,X30),k2_zfmisc_1(X29,X31)), inference(variable_rename,[status(thm)],[t123_zfmisc_1])).
% 0.19/0.39  cnf(c_0_29, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_30, plain, (r1_tarski(k4_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.19/0.39  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=k3_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.39  cnf(c_0_32, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.39  cnf(c_0_33, plain, (~r2_hidden(X1,k4_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_24])).
% 0.19/0.39  cnf(c_0_34, negated_conjecture, (r2_hidden(esk1_2(esk5_0,X1),k4_xboole_0(esk6_0,X2))|r2_hidden(esk1_2(esk5_0,X1),X2)|r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_35, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),esk4_0)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_27, c_0_15])).
% 0.19/0.39  cnf(c_0_36, negated_conjecture, (k3_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk4_0,esk5_0))!=k2_zfmisc_1(esk3_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.39  cnf(c_0_37, plain, (k2_zfmisc_1(k3_xboole_0(X1,X2),k3_xboole_0(X3,X4))=k3_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.39  cnf(c_0_38, plain, (k4_xboole_0(X1,X2)=X1|~r1_tarski(X1,k4_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.39  cnf(c_0_39, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k4_xboole_0(X2,k4_xboole_0(X2,X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_31, c_0_32]), c_0_32])).
% 0.19/0.39  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),k4_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_33, c_0_15])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (r2_hidden(esk1_2(esk5_0,k4_xboole_0(esk6_0,X1)),X1)|r1_tarski(esk5_0,k4_xboole_0(esk6_0,X1))), inference(spm,[status(thm)],[c_0_20, c_0_34])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (r2_hidden(esk1_2(esk3_0,X1),k4_xboole_0(esk4_0,X2))|r2_hidden(esk1_2(esk3_0,X1),X2)|r1_tarski(esk3_0,X1)), inference(spm,[status(thm)],[c_0_25, c_0_35])).
% 0.19/0.39  cnf(c_0_43, negated_conjecture, (k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k4_xboole_0(k2_zfmisc_1(esk3_0,esk6_0),k2_zfmisc_1(esk4_0,esk5_0)))!=k2_zfmisc_1(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_36, c_0_32])).
% 0.19/0.39  cnf(c_0_44, plain, (k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X3,k4_xboole_0(X3,X4)))=k4_xboole_0(k2_zfmisc_1(X1,X3),k4_xboole_0(k2_zfmisc_1(X1,X3),k2_zfmisc_1(X2,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_37, c_0_32]), c_0_32]), c_0_32])).
% 0.19/0.39  cnf(c_0_45, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=X2|~r1_tarski(X2,k4_xboole_0(X1,k4_xboole_0(X1,X2)))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (r1_tarski(esk5_0,k4_xboole_0(esk6_0,k4_xboole_0(X1,esk5_0)))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (r2_hidden(esk1_2(esk3_0,k4_xboole_0(esk4_0,X1)),X1)|r1_tarski(esk3_0,k4_xboole_0(esk4_0,X1))), inference(spm,[status(thm)],[c_0_20, c_0_42])).
% 0.19/0.39  cnf(c_0_48, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0)))!=k2_zfmisc_1(esk3_0,esk5_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44]), c_0_39])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (k4_xboole_0(esk5_0,k4_xboole_0(esk5_0,esk6_0))=esk5_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_39])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (r1_tarski(esk3_0,k4_xboole_0(esk4_0,k4_xboole_0(X1,esk3_0)))), inference(spm,[status(thm)],[c_0_40, c_0_47])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (k2_zfmisc_1(k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0)),esk5_0)!=k2_zfmisc_1(esk3_0,esk5_0)), inference(rw,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (k4_xboole_0(esk3_0,k4_xboole_0(esk3_0,esk4_0))=esk3_0), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_50]), c_0_39])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 54
% 0.19/0.39  # Proof object clause steps            : 39
% 0.19/0.39  # Proof object formula steps           : 15
% 0.19/0.39  # Proof object conjectures             : 22
% 0.19/0.39  # Proof object clause conjectures      : 19
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 13
% 0.19/0.39  # Proof object initial formulas used   : 7
% 0.19/0.39  # Proof object generating inferences   : 17
% 0.19/0.39  # Proof object simplifying inferences  : 16
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 9
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 20
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 19
% 0.19/0.39  # Processed clauses                    : 332
% 0.19/0.39  # ...of these trivial                  : 7
% 0.19/0.39  # ...subsumed                          : 195
% 0.19/0.39  # ...remaining for further processing  : 130
% 0.19/0.39  # Other redundant clauses eliminated   : 5
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 1
% 0.19/0.39  # Backward-rewritten                   : 17
% 0.19/0.39  # Generated clauses                    : 1361
% 0.19/0.39  # ...of the previous two non-trivial   : 1066
% 0.19/0.39  # Contextual simplify-reflections      : 2
% 0.19/0.39  # Paramodulations                      : 1354
% 0.19/0.39  # Factorizations                       : 2
% 0.19/0.39  # Equation resolutions                 : 5
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 89
% 0.19/0.39  #    Positive orientable unit clauses  : 17
% 0.19/0.39  #    Positive unorientable unit clauses: 2
% 0.19/0.39  #    Negative unit clauses             : 0
% 0.19/0.39  #    Non-unit-clauses                  : 70
% 0.19/0.39  # Current number of unprocessed clauses: 730
% 0.19/0.39  # ...number of literals in the above   : 1474
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 37
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 1135
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 1029
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 195
% 0.19/0.39  # Unit Clause-clause subsumption calls : 66
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 100
% 0.19/0.39  # BW rewrite match successes           : 25
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 20673
% 0.19/0.40  
% 0.19/0.40  # -------------------------------------------------
% 0.19/0.40  # User time                : 0.052 s
% 0.19/0.40  # System time              : 0.004 s
% 0.19/0.40  # Total time               : 0.056 s
% 0.19/0.40  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
