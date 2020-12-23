%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:47:13 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 122 expanded)
%              Number of clauses        :   27 (  59 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 235 expanded)
%              Number of equality atoms :   71 ( 156 expanded)
%              Maximal formula depth    :   17 (   3 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t41_enumset1,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(t10_setfam_1,axiom,(
    ! [X1,X2] :
      ~ ( X1 != k1_xboole_0
        & X2 != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(X1,X2)) != k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(t11_setfam_1,axiom,(
    ! [X1] : k1_setfam_1(k1_tarski(X1)) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(t12_setfam_1,conjecture,(
    ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(c_0_11,plain,(
    ! [X33,X34,X35,X36,X37,X38] :
      ( ( ~ r2_hidden(X35,X34)
        | X35 = X33
        | X34 != k1_tarski(X33) )
      & ( X36 != X33
        | r2_hidden(X36,X34)
        | X34 != k1_tarski(X33) )
      & ( ~ r2_hidden(esk3_2(X37,X38),X38)
        | esk3_2(X37,X38) != X37
        | X38 = k1_tarski(X37) )
      & ( r2_hidden(esk3_2(X37,X38),X38)
        | esk3_2(X37,X38) = X37
        | X38 = k1_tarski(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_12,plain,(
    ! [X42] : k2_tarski(X42,X42) = k1_tarski(X42) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_13,plain,(
    ! [X26] : k3_xboole_0(X26,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_14,plain,(
    ! [X28,X29] : k4_xboole_0(X28,k4_xboole_0(X28,X29)) = k3_xboole_0(X28,X29) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X7,X8,X9,X10,X11,X12,X13,X14] :
      ( ( ~ r2_hidden(X10,X9)
        | r2_hidden(X10,X7)
        | r2_hidden(X10,X8)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X7)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(X11,X8)
        | r2_hidden(X11,X9)
        | X9 != k2_xboole_0(X7,X8) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X12)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X12,X13,X14),X13)
        | ~ r2_hidden(esk1_3(X12,X13,X14),X14)
        | X14 = k2_xboole_0(X12,X13) )
      & ( r2_hidden(esk1_3(X12,X13,X14),X14)
        | r2_hidden(esk1_3(X12,X13,X14),X12)
        | r2_hidden(esk1_3(X12,X13,X14),X13)
        | X14 = k2_xboole_0(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_20,plain,(
    ! [X27] : k4_xboole_0(X27,k1_xboole_0) = X27 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

cnf(c_0_21,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

fof(c_0_23,plain,(
    ! [X40,X41] : k2_tarski(X40,X41) = k2_xboole_0(k1_tarski(X40),k1_tarski(X41)) ),
    inference(variable_rename,[status(thm)],[t41_enumset1])).

fof(c_0_24,plain,(
    ! [X45,X46,X47] :
      ( ( ~ r2_hidden(X45,X47)
        | k4_xboole_0(k2_tarski(X45,X46),X47) != k2_tarski(X45,X46) )
      & ( ~ r2_hidden(X46,X47)
        | k4_xboole_0(k2_tarski(X45,X46),X47) != k2_tarski(X45,X46) )
      & ( r2_hidden(X45,X47)
        | r2_hidden(X46,X47)
        | k4_xboole_0(k2_tarski(X45,X46),X47) = k2_tarski(X45,X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

cnf(c_0_25,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).

cnf(c_0_29,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k1_tarski(X1),k1_tarski(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_30,plain,(
    ! [X48,X49] :
      ( X48 = k1_xboole_0
      | X49 = k1_xboole_0
      | k1_setfam_1(k2_xboole_0(X48,X49)) = k3_xboole_0(k1_setfam_1(X48),k1_setfam_1(X49)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).

fof(c_0_31,plain,(
    ! [X50] : k1_setfam_1(k1_tarski(X50)) = X50 ),
    inference(variable_rename,[status(thm)],[t11_setfam_1])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X1,X1))) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,plain,
    ( k2_tarski(X1,X2) = k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29,c_0_17]),c_0_17])).

fof(c_0_36,negated_conjecture,(
    ~ ! [X1,X2] : k1_setfam_1(k2_tarski(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(assume_negation,[status(cth)],[t12_setfam_1])).

cnf(c_0_37,plain,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_38,plain,
    ( k1_setfam_1(k1_tarski(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_39,plain,
    ( k2_tarski(X1,X2) != k1_xboole_0
    | ~ r2_hidden(X2,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

fof(c_0_41,negated_conjecture,(
    k1_setfam_1(k2_tarski(esk4_0,esk5_0)) != k3_xboole_0(esk4_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).

cnf(c_0_42,plain,
    ( X2 = k1_xboole_0
    | X1 = k1_xboole_0
    | k1_setfam_1(k2_xboole_0(X1,X2)) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))) ),
    inference(rw,[status(thm)],[c_0_37,c_0_19])).

cnf(c_0_43,plain,
    ( k1_setfam_1(k2_tarski(X1,X1)) = X1 ),
    inference(rw,[status(thm)],[c_0_38,c_0_17])).

cnf(c_0_44,plain,
    ( k2_tarski(X1,X2) != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_40])])).

cnf(c_0_45,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,esk5_0)) != k3_xboole_0(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,plain,
    ( k1_setfam_1(k2_xboole_0(k2_tarski(X1,X1),X2)) = k4_xboole_0(X1,k4_xboole_0(X1,k1_setfam_1(X2)))
    | X2 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( k1_setfam_1(k2_tarski(esk4_0,esk5_0)) != k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_19])).

cnf(c_0_48,plain,
    ( k1_setfam_1(k2_tarski(X1,X2)) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_35]),c_0_43]),c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47,c_0_48])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.37  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.37  # and selection function SelectNegativeLiterals.
% 0.20/0.37  #
% 0.20/0.37  # Preprocessing time       : 0.029 s
% 0.20/0.37  # Presaturation interreduction done
% 0.20/0.37  
% 0.20/0.37  # Proof found!
% 0.20/0.37  # SZS status Theorem
% 0.20/0.37  # SZS output start CNFRefutation
% 0.20/0.37  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.20/0.37  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.20/0.37  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.37  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.37  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.20/0.37  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.37  fof(t41_enumset1, axiom, ![X1, X2]:k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 0.20/0.37  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.20/0.37  fof(t10_setfam_1, axiom, ![X1, X2]:~(((X1!=k1_xboole_0&X2!=k1_xboole_0)&k1_setfam_1(k2_xboole_0(X1,X2))!=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 0.20/0.37  fof(t11_setfam_1, axiom, ![X1]:k1_setfam_1(k1_tarski(X1))=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 0.20/0.37  fof(t12_setfam_1, conjecture, ![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 0.20/0.37  fof(c_0_11, plain, ![X33, X34, X35, X36, X37, X38]:(((~r2_hidden(X35,X34)|X35=X33|X34!=k1_tarski(X33))&(X36!=X33|r2_hidden(X36,X34)|X34!=k1_tarski(X33)))&((~r2_hidden(esk3_2(X37,X38),X38)|esk3_2(X37,X38)!=X37|X38=k1_tarski(X37))&(r2_hidden(esk3_2(X37,X38),X38)|esk3_2(X37,X38)=X37|X38=k1_tarski(X37)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.20/0.37  fof(c_0_12, plain, ![X42]:k2_tarski(X42,X42)=k1_tarski(X42), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.20/0.37  fof(c_0_13, plain, ![X26]:k3_xboole_0(X26,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.37  fof(c_0_14, plain, ![X28, X29]:k4_xboole_0(X28,k4_xboole_0(X28,X29))=k3_xboole_0(X28,X29), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.37  fof(c_0_15, plain, ![X7, X8, X9, X10, X11, X12, X13, X14]:(((~r2_hidden(X10,X9)|(r2_hidden(X10,X7)|r2_hidden(X10,X8))|X9!=k2_xboole_0(X7,X8))&((~r2_hidden(X11,X7)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))&(~r2_hidden(X11,X8)|r2_hidden(X11,X9)|X9!=k2_xboole_0(X7,X8))))&(((~r2_hidden(esk1_3(X12,X13,X14),X12)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13))&(~r2_hidden(esk1_3(X12,X13,X14),X13)|~r2_hidden(esk1_3(X12,X13,X14),X14)|X14=k2_xboole_0(X12,X13)))&(r2_hidden(esk1_3(X12,X13,X14),X14)|(r2_hidden(esk1_3(X12,X13,X14),X12)|r2_hidden(esk1_3(X12,X13,X14),X13))|X14=k2_xboole_0(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.20/0.37  cnf(c_0_16, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.37  cnf(c_0_17, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.37  cnf(c_0_18, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.37  cnf(c_0_19, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.37  fof(c_0_20, plain, ![X27]:k4_xboole_0(X27,k1_xboole_0)=X27, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.37  cnf(c_0_21, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.37  cnf(c_0_22, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.37  fof(c_0_23, plain, ![X40, X41]:k2_tarski(X40,X41)=k2_xboole_0(k1_tarski(X40),k1_tarski(X41)), inference(variable_rename,[status(thm)],[t41_enumset1])).
% 0.20/0.37  fof(c_0_24, plain, ![X45, X46, X47]:(((~r2_hidden(X45,X47)|k4_xboole_0(k2_tarski(X45,X46),X47)!=k2_tarski(X45,X46))&(~r2_hidden(X46,X47)|k4_xboole_0(k2_tarski(X45,X46),X47)!=k2_tarski(X45,X46)))&(r2_hidden(X45,X47)|r2_hidden(X46,X47)|k4_xboole_0(k2_tarski(X45,X46),X47)=k2_tarski(X45,X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.20/0.37  cnf(c_0_25, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.37  cnf(c_0_26, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.37  cnf(c_0_27, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_21])).
% 0.20/0.37  cnf(c_0_28, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_22])])).
% 0.20/0.37  cnf(c_0_29, plain, (k2_tarski(X1,X2)=k2_xboole_0(k1_tarski(X1),k1_tarski(X2))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.37  fof(c_0_30, plain, ![X48, X49]:(X48=k1_xboole_0|X49=k1_xboole_0|k1_setfam_1(k2_xboole_0(X48,X49))=k3_xboole_0(k1_setfam_1(X48),k1_setfam_1(X49))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_setfam_1])])).
% 0.20/0.37  fof(c_0_31, plain, ![X50]:k1_setfam_1(k1_tarski(X50))=X50, inference(variable_rename,[status(thm)],[t11_setfam_1])).
% 0.20/0.37  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.37  cnf(c_0_33, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.37  cnf(c_0_34, plain, (r2_hidden(X1,k2_xboole_0(X2,k2_tarski(X1,X1)))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.37  cnf(c_0_35, plain, (k2_tarski(X1,X2)=k2_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_29, c_0_17]), c_0_17])).
% 0.20/0.37  fof(c_0_36, negated_conjecture, ~(![X1, X2]:k1_setfam_1(k2_tarski(X1,X2))=k3_xboole_0(X1,X2)), inference(assume_negation,[status(cth)],[t12_setfam_1])).
% 0.20/0.37  cnf(c_0_37, plain, (X1=k1_xboole_0|X2=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k3_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.37  cnf(c_0_38, plain, (k1_setfam_1(k1_tarski(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.20/0.37  cnf(c_0_39, plain, (k2_tarski(X1,X2)!=k1_xboole_0|~r2_hidden(X2,k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.37  cnf(c_0_40, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.20/0.37  fof(c_0_41, negated_conjecture, k1_setfam_1(k2_tarski(esk4_0,esk5_0))!=k3_xboole_0(esk4_0,esk5_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_36])])])).
% 0.20/0.37  cnf(c_0_42, plain, (X2=k1_xboole_0|X1=k1_xboole_0|k1_setfam_1(k2_xboole_0(X1,X2))=k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),k1_setfam_1(X2)))), inference(rw,[status(thm)],[c_0_37, c_0_19])).
% 0.20/0.37  cnf(c_0_43, plain, (k1_setfam_1(k2_tarski(X1,X1))=X1), inference(rw,[status(thm)],[c_0_38, c_0_17])).
% 0.20/0.37  cnf(c_0_44, plain, (k2_tarski(X1,X2)!=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_40])])).
% 0.20/0.37  cnf(c_0_45, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,esk5_0))!=k3_xboole_0(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.20/0.37  cnf(c_0_46, plain, (k1_setfam_1(k2_xboole_0(k2_tarski(X1,X1),X2))=k4_xboole_0(X1,k4_xboole_0(X1,k1_setfam_1(X2)))|X2=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_43]), c_0_44])).
% 0.20/0.37  cnf(c_0_47, negated_conjecture, (k1_setfam_1(k2_tarski(esk4_0,esk5_0))!=k4_xboole_0(esk4_0,k4_xboole_0(esk4_0,esk5_0))), inference(rw,[status(thm)],[c_0_45, c_0_19])).
% 0.20/0.37  cnf(c_0_48, plain, (k1_setfam_1(k2_tarski(X1,X2))=k4_xboole_0(X1,k4_xboole_0(X1,X2))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_35]), c_0_43]), c_0_44])).
% 0.20/0.37  cnf(c_0_49, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_47, c_0_48])]), ['proof']).
% 0.20/0.37  # SZS output end CNFRefutation
% 0.20/0.37  # Proof object total steps             : 50
% 0.20/0.37  # Proof object clause steps            : 27
% 0.20/0.37  # Proof object formula steps           : 23
% 0.20/0.37  # Proof object conjectures             : 6
% 0.20/0.37  # Proof object clause conjectures      : 3
% 0.20/0.37  # Proof object formula conjectures     : 3
% 0.20/0.37  # Proof object initial clauses used    : 11
% 0.20/0.37  # Proof object initial formulas used   : 11
% 0.20/0.37  # Proof object generating inferences   : 5
% 0.20/0.37  # Proof object simplifying inferences  : 18
% 0.20/0.37  # Training examples: 0 positive, 0 negative
% 0.20/0.37  # Parsed axioms                        : 17
% 0.20/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.37  # Initial clauses                      : 32
% 0.20/0.37  # Removed in clause preprocessing      : 2
% 0.20/0.37  # Initial clauses in saturation        : 30
% 0.20/0.37  # Processed clauses                    : 113
% 0.20/0.37  # ...of these trivial                  : 2
% 0.20/0.37  # ...subsumed                          : 38
% 0.20/0.37  # ...remaining for further processing  : 73
% 0.20/0.37  # Other redundant clauses eliminated   : 9
% 0.20/0.37  # Clauses deleted for lack of memory   : 0
% 0.20/0.37  # Backward-subsumed                    : 0
% 0.20/0.37  # Backward-rewritten                   : 6
% 0.20/0.37  # Generated clauses                    : 154
% 0.20/0.37  # ...of the previous two non-trivial   : 109
% 0.20/0.37  # Contextual simplify-reflections      : 0
% 0.20/0.37  # Paramodulations                      : 146
% 0.20/0.37  # Factorizations                       : 0
% 0.20/0.37  # Equation resolutions                 : 9
% 0.20/0.37  # Propositional unsat checks           : 0
% 0.20/0.37  #    Propositional check models        : 0
% 0.20/0.37  #    Propositional check unsatisfiable : 0
% 0.20/0.37  #    Propositional clauses             : 0
% 0.20/0.37  #    Propositional clauses after purity: 0
% 0.20/0.37  #    Propositional unsat core size     : 0
% 0.20/0.37  #    Propositional preprocessing time  : 0.000
% 0.20/0.37  #    Propositional encoding time       : 0.000
% 0.20/0.37  #    Propositional solver time         : 0.000
% 0.20/0.37  #    Success case prop preproc time    : 0.000
% 0.20/0.37  #    Success case prop encoding time   : 0.000
% 0.20/0.37  #    Success case prop solver time     : 0.000
% 0.20/0.37  # Current number of processed clauses  : 30
% 0.20/0.37  #    Positive orientable unit clauses  : 8
% 0.20/0.37  #    Positive unorientable unit clauses: 3
% 0.20/0.37  #    Negative unit clauses             : 2
% 0.20/0.37  #    Non-unit-clauses                  : 17
% 0.20/0.37  # Current number of unprocessed clauses: 53
% 0.20/0.37  # ...number of literals in the above   : 130
% 0.20/0.37  # Current number of archived formulas  : 0
% 0.20/0.37  # Current number of archived clauses   : 37
% 0.20/0.37  # Clause-clause subsumption calls (NU) : 135
% 0.20/0.37  # Rec. Clause-clause subsumption calls : 106
% 0.20/0.37  # Non-unit clause-clause subsumptions  : 16
% 0.20/0.37  # Unit Clause-clause subsumption calls : 9
% 0.20/0.37  # Rewrite failures with RHS unbound    : 0
% 0.20/0.37  # BW rewrite match attempts            : 45
% 0.20/0.37  # BW rewrite match successes           : 29
% 0.20/0.37  # Condensation attempts                : 0
% 0.20/0.37  # Condensation successes               : 0
% 0.20/0.37  # Termbank termtop insertions          : 3214
% 0.20/0.37  
% 0.20/0.37  # -------------------------------------------------
% 0.20/0.37  # User time                : 0.035 s
% 0.20/0.37  # System time              : 0.002 s
% 0.20/0.37  # Total time               : 0.037 s
% 0.20/0.37  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
