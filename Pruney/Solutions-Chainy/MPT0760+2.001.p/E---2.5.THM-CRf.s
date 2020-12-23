%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:56:42 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 (  74 expanded)
%              Number of clauses        :   31 (  34 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 194 expanded)
%              Number of equality atoms :   52 (  67 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(commutativity_k2_xboole_0,axiom,(
    ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(t2_wellord1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k3_relat_1(X2))
        | k1_wellord1(X2,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(d1_wellord1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k1_wellord1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ( X4 != X2
                & r2_hidden(k4_tarski(X4,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_13,plain,(
    ! [X22] : k3_xboole_0(X22,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_14,plain,(
    ! [X25,X26] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k3_xboole_0(X25,X26) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_15,plain,(
    ! [X13,X14,X15,X16,X17,X18,X19,X20] :
      ( ( r2_hidden(X16,X13)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( r2_hidden(X16,X14)
        | ~ r2_hidden(X16,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(X17,X13)
        | ~ r2_hidden(X17,X14)
        | r2_hidden(X17,X15)
        | X15 != k3_xboole_0(X13,X14) )
      & ( ~ r2_hidden(esk2_3(X18,X19,X20),X20)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X18)
        | ~ r2_hidden(esk2_3(X18,X19,X20),X19)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X18)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) )
      & ( r2_hidden(esk2_3(X18,X19,X20),X19)
        | r2_hidden(esk2_3(X18,X19,X20),X20)
        | X20 = k3_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

cnf(c_0_16,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X24] : k4_xboole_0(X24,k1_xboole_0) = X24 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_19,plain,(
    ! [X41,X42] :
      ( ~ r2_hidden(X41,X42)
      | ~ r1_tarski(X42,X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

fof(c_0_20,plain,(
    ! [X23] : r1_tarski(k1_xboole_0,X23) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_21,plain,(
    ! [X40] :
      ( ~ v1_relat_1(X40)
      | k3_relat_1(X40) = k2_xboole_0(k1_relat_1(X40),k2_relat_1(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_22,plain,(
    ! [X5,X6] : k2_xboole_0(X5,X6) = k2_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).

fof(c_0_23,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          | k1_wellord1(X2,X1) = k1_xboole_0 ) ) ),
    inference(assume_negation,[status(cth)],[t2_wellord1])).

fof(c_0_24,plain,(
    ! [X43,X44,X45,X46,X47,X48,X49] :
      ( ( X46 != X44
        | ~ r2_hidden(X46,X45)
        | X45 != k1_wellord1(X43,X44)
        | ~ v1_relat_1(X43) )
      & ( r2_hidden(k4_tarski(X46,X44),X43)
        | ~ r2_hidden(X46,X45)
        | X45 != k1_wellord1(X43,X44)
        | ~ v1_relat_1(X43) )
      & ( X47 = X44
        | ~ r2_hidden(k4_tarski(X47,X44),X43)
        | r2_hidden(X47,X45)
        | X45 != k1_wellord1(X43,X44)
        | ~ v1_relat_1(X43) )
      & ( ~ r2_hidden(esk6_3(X43,X48,X49),X49)
        | esk6_3(X43,X48,X49) = X48
        | ~ r2_hidden(k4_tarski(esk6_3(X43,X48,X49),X48),X43)
        | X49 = k1_wellord1(X43,X48)
        | ~ v1_relat_1(X43) )
      & ( esk6_3(X43,X48,X49) != X48
        | r2_hidden(esk6_3(X43,X48,X49),X49)
        | X49 = k1_wellord1(X43,X48)
        | ~ v1_relat_1(X43) )
      & ( r2_hidden(k4_tarski(esk6_3(X43,X48,X49),X48),X43)
        | r2_hidden(esk6_3(X43,X48,X49),X49)
        | X49 = k1_wellord1(X43,X48)
        | ~ v1_relat_1(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).

cnf(c_0_25,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | X3 = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_27,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

fof(c_0_32,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & ~ r2_hidden(esk7_0,k3_relat_1(esk8_0))
    & k1_wellord1(esk8_0,esk7_0) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).

cnf(c_0_33,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X4 != k1_wellord1(X3,X2)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,plain,
    ( X3 = k4_xboole_0(X1,k4_xboole_0(X1,X2))
    | r2_hidden(esk2_3(X1,X2,X3),X3)
    | r2_hidden(esk2_3(X1,X2,X3),X2) ),
    inference(rw,[status(thm)],[c_0_25,c_0_17])).

cnf(c_0_35,plain,
    ( k4_xboole_0(X1,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_37,plain,(
    ! [X27,X28] : r1_tarski(X27,k2_xboole_0(X27,X28)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(k2_relat_1(X1),k1_relat_1(X1)) = k3_relat_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(rw,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_40,plain,(
    ! [X29,X30,X31,X33,X34,X35,X36,X38] :
      ( ( ~ r2_hidden(X31,X30)
        | r2_hidden(k4_tarski(esk3_3(X29,X30,X31),X31),X29)
        | X30 != k2_relat_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X34,X33),X29)
        | r2_hidden(X33,X30)
        | X30 != k2_relat_1(X29) )
      & ( ~ r2_hidden(esk4_2(X35,X36),X36)
        | ~ r2_hidden(k4_tarski(X38,esk4_2(X35,X36)),X35)
        | X36 = k2_relat_1(X35) )
      & ( r2_hidden(esk4_2(X35,X36),X36)
        | r2_hidden(k4_tarski(esk5_2(X35,X36),esk4_2(X35,X36)),X35)
        | X36 = k2_relat_1(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_41,plain,
    ( r2_hidden(k4_tarski(X1,X2),X3)
    | ~ v1_relat_1(X3)
    | ~ r2_hidden(X1,k1_wellord1(X3,X2)) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( k1_wellord1(esk8_0,esk7_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_35]),c_0_36])).

fof(c_0_44,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_45,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( k2_xboole_0(k2_relat_1(esk8_0),k1_relat_1(esk8_0)) = k3_relat_1(esk8_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),esk8_0)
    | ~ r2_hidden(X1,k1_wellord1(esk8_0,X2)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_39])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk2_3(X1,k1_xboole_0,k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_50,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_3(X1,k1_xboole_0,k1_wellord1(esk8_0,esk7_0)),esk7_0),esk8_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(X1,k3_relat_1(esk8_0))
    | ~ r2_hidden(X1,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk7_0,k2_relat_1(esk8_0)) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(esk7_0,k3_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:40:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.34  # No SInE strategy applied
% 0.11/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.36  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.36  # and selection function SelectNegativeLiterals.
% 0.20/0.36  #
% 0.20/0.36  # Preprocessing time       : 0.017 s
% 0.20/0.36  # Presaturation interreduction done
% 0.20/0.36  
% 0.20/0.36  # Proof found!
% 0.20/0.36  # SZS status Theorem
% 0.20/0.36  # SZS output start CNFRefutation
% 0.20/0.36  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.20/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.20/0.36  fof(d4_xboole_0, axiom, ![X1, X2, X3]:(X3=k3_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 0.20/0.36  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.20/0.36  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.20/0.36  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.36  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 0.20/0.36  fof(commutativity_k2_xboole_0, axiom, ![X1, X2]:k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 0.20/0.36  fof(t2_wellord1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k3_relat_1(X2))|k1_wellord1(X2,X1)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord1)).
% 0.20/0.36  fof(d1_wellord1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k1_wellord1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4!=X2&r2_hidden(k4_tarski(X4,X2),X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 0.20/0.36  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.36  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.20/0.36  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.36  fof(c_0_13, plain, ![X22]:k3_xboole_0(X22,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.20/0.36  fof(c_0_14, plain, ![X25, X26]:k4_xboole_0(X25,k4_xboole_0(X25,X26))=k3_xboole_0(X25,X26), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.20/0.36  fof(c_0_15, plain, ![X13, X14, X15, X16, X17, X18, X19, X20]:((((r2_hidden(X16,X13)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14))&(r2_hidden(X16,X14)|~r2_hidden(X16,X15)|X15!=k3_xboole_0(X13,X14)))&(~r2_hidden(X17,X13)|~r2_hidden(X17,X14)|r2_hidden(X17,X15)|X15!=k3_xboole_0(X13,X14)))&((~r2_hidden(esk2_3(X18,X19,X20),X20)|(~r2_hidden(esk2_3(X18,X19,X20),X18)|~r2_hidden(esk2_3(X18,X19,X20),X19))|X20=k3_xboole_0(X18,X19))&((r2_hidden(esk2_3(X18,X19,X20),X18)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))&(r2_hidden(esk2_3(X18,X19,X20),X19)|r2_hidden(esk2_3(X18,X19,X20),X20)|X20=k3_xboole_0(X18,X19))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).
% 0.20/0.36  cnf(c_0_16, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.36  cnf(c_0_17, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.36  fof(c_0_18, plain, ![X24]:k4_xboole_0(X24,k1_xboole_0)=X24, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.20/0.36  fof(c_0_19, plain, ![X41, X42]:(~r2_hidden(X41,X42)|~r1_tarski(X42,X41)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.20/0.36  fof(c_0_20, plain, ![X23]:r1_tarski(k1_xboole_0,X23), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.36  fof(c_0_21, plain, ![X40]:(~v1_relat_1(X40)|k3_relat_1(X40)=k2_xboole_0(k1_relat_1(X40),k2_relat_1(X40))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.20/0.36  fof(c_0_22, plain, ![X5, X6]:k2_xboole_0(X5,X6)=k2_xboole_0(X6,X5), inference(variable_rename,[status(thm)],[commutativity_k2_xboole_0])).
% 0.20/0.36  fof(c_0_23, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k3_relat_1(X2))|k1_wellord1(X2,X1)=k1_xboole_0))), inference(assume_negation,[status(cth)],[t2_wellord1])).
% 0.20/0.36  fof(c_0_24, plain, ![X43, X44, X45, X46, X47, X48, X49]:((((X46!=X44|~r2_hidden(X46,X45)|X45!=k1_wellord1(X43,X44)|~v1_relat_1(X43))&(r2_hidden(k4_tarski(X46,X44),X43)|~r2_hidden(X46,X45)|X45!=k1_wellord1(X43,X44)|~v1_relat_1(X43)))&(X47=X44|~r2_hidden(k4_tarski(X47,X44),X43)|r2_hidden(X47,X45)|X45!=k1_wellord1(X43,X44)|~v1_relat_1(X43)))&((~r2_hidden(esk6_3(X43,X48,X49),X49)|(esk6_3(X43,X48,X49)=X48|~r2_hidden(k4_tarski(esk6_3(X43,X48,X49),X48),X43))|X49=k1_wellord1(X43,X48)|~v1_relat_1(X43))&((esk6_3(X43,X48,X49)!=X48|r2_hidden(esk6_3(X43,X48,X49),X49)|X49=k1_wellord1(X43,X48)|~v1_relat_1(X43))&(r2_hidden(k4_tarski(esk6_3(X43,X48,X49),X48),X43)|r2_hidden(esk6_3(X43,X48,X49),X49)|X49=k1_wellord1(X43,X48)|~v1_relat_1(X43))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_wellord1])])])])])])).
% 0.20/0.36  cnf(c_0_25, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r2_hidden(esk2_3(X1,X2,X3),X3)|X3=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.36  cnf(c_0_26, plain, (k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))=k1_xboole_0), inference(rw,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.36  cnf(c_0_27, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.36  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.36  cnf(c_0_29, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.36  cnf(c_0_30, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.36  cnf(c_0_31, plain, (k2_xboole_0(X1,X2)=k2_xboole_0(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.36  fof(c_0_32, negated_conjecture, (v1_relat_1(esk8_0)&(~r2_hidden(esk7_0,k3_relat_1(esk8_0))&k1_wellord1(esk8_0,esk7_0)!=k1_xboole_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_23])])])).
% 0.20/0.36  cnf(c_0_33, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X4!=k1_wellord1(X3,X2)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.36  cnf(c_0_34, plain, (X3=k4_xboole_0(X1,k4_xboole_0(X1,X2))|r2_hidden(esk2_3(X1,X2,X3),X3)|r2_hidden(esk2_3(X1,X2,X3),X2)), inference(rw,[status(thm)],[c_0_25, c_0_17])).
% 0.20/0.36  cnf(c_0_35, plain, (k4_xboole_0(X1,X1)=k1_xboole_0), inference(rw,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.36  cnf(c_0_36, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.36  fof(c_0_37, plain, ![X27, X28]:r1_tarski(X27,k2_xboole_0(X27,X28)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.36  cnf(c_0_38, plain, (k2_xboole_0(k2_relat_1(X1),k1_relat_1(X1))=k3_relat_1(X1)|~v1_relat_1(X1)), inference(rw,[status(thm)],[c_0_30, c_0_31])).
% 0.20/0.36  cnf(c_0_39, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.36  fof(c_0_40, plain, ![X29, X30, X31, X33, X34, X35, X36, X38]:(((~r2_hidden(X31,X30)|r2_hidden(k4_tarski(esk3_3(X29,X30,X31),X31),X29)|X30!=k2_relat_1(X29))&(~r2_hidden(k4_tarski(X34,X33),X29)|r2_hidden(X33,X30)|X30!=k2_relat_1(X29)))&((~r2_hidden(esk4_2(X35,X36),X36)|~r2_hidden(k4_tarski(X38,esk4_2(X35,X36)),X35)|X36=k2_relat_1(X35))&(r2_hidden(esk4_2(X35,X36),X36)|r2_hidden(k4_tarski(esk5_2(X35,X36),esk4_2(X35,X36)),X35)|X36=k2_relat_1(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.20/0.36  cnf(c_0_41, plain, (r2_hidden(k4_tarski(X1,X2),X3)|~v1_relat_1(X3)|~r2_hidden(X1,k1_wellord1(X3,X2))), inference(er,[status(thm)],[c_0_33])).
% 0.20/0.36  cnf(c_0_42, negated_conjecture, (k1_wellord1(esk8_0,esk7_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.36  cnf(c_0_43, plain, (X1=k1_xboole_0|r2_hidden(esk2_3(X2,k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_35]), c_0_36])).
% 0.20/0.36  fof(c_0_44, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.36  cnf(c_0_45, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.36  cnf(c_0_46, negated_conjecture, (k2_xboole_0(k2_relat_1(esk8_0),k1_relat_1(esk8_0))=k3_relat_1(esk8_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.20/0.36  cnf(c_0_47, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.20/0.36  cnf(c_0_48, negated_conjecture, (r2_hidden(k4_tarski(X1,X2),esk8_0)|~r2_hidden(X1,k1_wellord1(esk8_0,X2))), inference(spm,[status(thm)],[c_0_41, c_0_39])).
% 0.20/0.36  cnf(c_0_49, negated_conjecture, (r2_hidden(esk2_3(X1,k1_xboole_0,k1_wellord1(esk8_0,esk7_0)),k1_wellord1(esk8_0,esk7_0))), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.36  cnf(c_0_50, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.36  cnf(c_0_51, negated_conjecture, (r1_tarski(k2_relat_1(esk8_0),k3_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.36  cnf(c_0_52, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_47])).
% 0.20/0.36  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk2_3(X1,k1_xboole_0,k1_wellord1(esk8_0,esk7_0)),esk7_0),esk8_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.36  cnf(c_0_54, negated_conjecture, (r2_hidden(X1,k3_relat_1(esk8_0))|~r2_hidden(X1,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.20/0.36  cnf(c_0_55, negated_conjecture, (r2_hidden(esk7_0,k2_relat_1(esk8_0))), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.36  cnf(c_0_56, negated_conjecture, (~r2_hidden(esk7_0,k3_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.36  cnf(c_0_57, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), ['proof']).
% 0.20/0.36  # SZS output end CNFRefutation
% 0.20/0.36  # Proof object total steps             : 58
% 0.20/0.36  # Proof object clause steps            : 31
% 0.20/0.36  # Proof object formula steps           : 27
% 0.20/0.36  # Proof object conjectures             : 14
% 0.20/0.36  # Proof object clause conjectures      : 11
% 0.20/0.36  # Proof object formula conjectures     : 3
% 0.20/0.36  # Proof object initial clauses used    : 15
% 0.20/0.36  # Proof object initial formulas used   : 13
% 0.20/0.36  # Proof object generating inferences   : 10
% 0.20/0.36  # Proof object simplifying inferences  : 9
% 0.20/0.36  # Training examples: 0 positive, 0 negative
% 0.20/0.36  # Parsed axioms                        : 13
% 0.20/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.36  # Initial clauses                      : 30
% 0.20/0.36  # Removed in clause preprocessing      : 1
% 0.20/0.36  # Initial clauses in saturation        : 29
% 0.20/0.36  # Processed clauses                    : 181
% 0.20/0.36  # ...of these trivial                  : 1
% 0.20/0.36  # ...subsumed                          : 64
% 0.20/0.36  # ...remaining for further processing  : 116
% 0.20/0.36  # Other redundant clauses eliminated   : 13
% 0.20/0.36  # Clauses deleted for lack of memory   : 0
% 0.20/0.36  # Backward-subsumed                    : 1
% 0.20/0.36  # Backward-rewritten                   : 0
% 0.20/0.36  # Generated clauses                    : 459
% 0.20/0.36  # ...of the previous two non-trivial   : 422
% 0.20/0.36  # Contextual simplify-reflections      : 0
% 0.20/0.36  # Paramodulations                      : 447
% 0.20/0.36  # Factorizations                       : 0
% 0.20/0.36  # Equation resolutions                 : 13
% 0.20/0.36  # Propositional unsat checks           : 0
% 0.20/0.36  #    Propositional check models        : 0
% 0.20/0.36  #    Propositional check unsatisfiable : 0
% 0.20/0.36  #    Propositional clauses             : 0
% 0.20/0.36  #    Propositional clauses after purity: 0
% 0.20/0.36  #    Propositional unsat core size     : 0
% 0.20/0.36  #    Propositional preprocessing time  : 0.000
% 0.20/0.36  #    Propositional encoding time       : 0.000
% 0.20/0.36  #    Propositional solver time         : 0.000
% 0.20/0.36  #    Success case prop preproc time    : 0.000
% 0.20/0.36  #    Success case prop encoding time   : 0.000
% 0.20/0.36  #    Success case prop solver time     : 0.000
% 0.20/0.36  # Current number of processed clauses  : 78
% 0.20/0.36  #    Positive orientable unit clauses  : 12
% 0.20/0.36  #    Positive unorientable unit clauses: 1
% 0.20/0.36  #    Negative unit clauses             : 8
% 0.20/0.36  #    Non-unit-clauses                  : 57
% 0.20/0.36  # Current number of unprocessed clauses: 290
% 0.20/0.36  # ...number of literals in the above   : 994
% 0.20/0.36  # Current number of archived formulas  : 0
% 0.20/0.36  # Current number of archived clauses   : 31
% 0.20/0.36  # Clause-clause subsumption calls (NU) : 832
% 0.20/0.36  # Rec. Clause-clause subsumption calls : 695
% 0.20/0.36  # Non-unit clause-clause subsumptions  : 39
% 0.20/0.36  # Unit Clause-clause subsumption calls : 22
% 0.20/0.36  # Rewrite failures with RHS unbound    : 0
% 0.20/0.36  # BW rewrite match attempts            : 5
% 0.20/0.36  # BW rewrite match successes           : 2
% 0.20/0.36  # Condensation attempts                : 0
% 0.20/0.36  # Condensation successes               : 0
% 0.20/0.36  # Termbank termtop insertions          : 8324
% 0.20/0.36  
% 0.20/0.36  # -------------------------------------------------
% 0.20/0.36  # User time                : 0.021 s
% 0.20/0.36  # System time              : 0.005 s
% 0.20/0.36  # Total time               : 0.027 s
% 0.20/0.36  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
