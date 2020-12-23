%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:50:44 EST 2020

% Result     : Theorem 0.77s
% Output     : CNFRefutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   47 (  85 expanded)
%              Number of clauses        :   27 (  37 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 294 expanded)
%              Number of equality atoms :   35 (  68 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d13_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X5,X4),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(t148_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => k2_relat_1(k7_relat_1(X2,X1)) = k9_relat_1(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(t151_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k9_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

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

fof(c_0_10,plain,(
    ! [X20,X21,X22,X23,X25,X26,X27,X28,X30] :
      ( ( r2_hidden(k4_tarski(esk3_4(X20,X21,X22,X23),X23),X20)
        | ~ r2_hidden(X23,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk3_4(X20,X21,X22,X23),X21)
        | ~ r2_hidden(X23,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(X26,X25),X20)
        | ~ r2_hidden(X26,X21)
        | r2_hidden(X25,X22)
        | X22 != k9_relat_1(X20,X21)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(esk4_3(X20,X27,X28),X28)
        | ~ r2_hidden(k4_tarski(X30,esk4_3(X20,X27,X28)),X20)
        | ~ r2_hidden(X30,X27)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(k4_tarski(esk5_3(X20,X27,X28),esk4_3(X20,X27,X28)),X20)
        | r2_hidden(esk4_3(X20,X27,X28),X28)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk5_3(X20,X27,X28),X27)
        | r2_hidden(esk4_3(X20,X27,X28),X28)
        | X28 = k9_relat_1(X20,X27)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).

fof(c_0_11,plain,(
    ! [X32,X33,X34,X36,X37,X38,X39,X41] :
      ( ( ~ r2_hidden(X34,X33)
        | r2_hidden(k4_tarski(X34,esk6_3(X32,X33,X34)),X32)
        | X33 != k1_relat_1(X32) )
      & ( ~ r2_hidden(k4_tarski(X36,X37),X32)
        | r2_hidden(X36,X33)
        | X33 != k1_relat_1(X32) )
      & ( ~ r2_hidden(esk7_2(X38,X39),X39)
        | ~ r2_hidden(k4_tarski(esk7_2(X38,X39),X41),X38)
        | X39 = k1_relat_1(X38) )
      & ( r2_hidden(esk7_2(X38,X39),X39)
        | r2_hidden(k4_tarski(esk7_2(X38,X39),esk8_2(X38,X39)),X38)
        | X39 = k1_relat_1(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_12,plain,(
    ! [X43,X44] :
      ( ~ v1_relat_1(X44)
      | k2_relat_1(k7_relat_1(X44,X43)) = k9_relat_1(X44,X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).

fof(c_0_13,plain,(
    ! [X45,X46] :
      ( ( k7_relat_1(X46,X45) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X46),X45)
        | ~ v1_relat_1(X46) )
      & ( ~ r1_xboole_0(k1_relat_1(X46),X45)
        | k7_relat_1(X46,X45) = k1_xboole_0
        | ~ v1_relat_1(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k9_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t151_relat_1])).

cnf(c_0_15,plain,
    ( r2_hidden(X2,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X1,X4)
    | X5 != k9_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_20,negated_conjecture,
    ( v1_relat_1(esk10_0)
    & ( k9_relat_1(esk10_0,esk9_0) != k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(esk10_0),esk9_0) )
    & ( k9_relat_1(esk10_0,esk9_0) = k1_xboole_0
      | r1_xboole_0(k1_relat_1(esk10_0),esk9_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_21,plain,(
    ! [X12,X13,X15,X16,X17] :
      ( ( r1_xboole_0(X12,X13)
        | r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)) )
      & ( ~ r2_hidden(X17,k3_xboole_0(X15,X16))
        | ~ r1_xboole_0(X15,X16) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_22,plain,(
    ! [X18] : k3_xboole_0(X18,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_23,plain,(
    ! [X19] : r1_xboole_0(X19,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k9_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X4,X1),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( r2_hidden(k4_tarski(X1,esk6_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_16])).

cnf(c_0_26,plain,
    ( k9_relat_1(X1,X2) = k1_xboole_0
    | ~ v1_relat_1(X1)
    | ~ r1_xboole_0(k1_relat_1(X1),X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( k9_relat_1(esk10_0,esk9_0) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,negated_conjecture,
    ( v1_relat_1(esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r2_hidden(esk1_2(X6,X7),X6)
        | r1_xboole_0(X6,X7) )
      & ( r2_hidden(esk1_2(X6,X7),X7)
        | r1_xboole_0(X6,X7) )
      & ( ~ r2_hidden(X11,X9)
        | ~ r2_hidden(X11,X10)
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_33,plain,
    ( r2_hidden(esk6_3(X1,k1_relat_1(X1),X2),k9_relat_1(X1,X3))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( k9_relat_1(esk10_0,esk9_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_37,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_38,negated_conjecture,
    ( ~ r2_hidden(X1,k1_relat_1(esk10_0))
    | ~ r2_hidden(X1,esk9_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])]),c_0_35])).

cnf(c_0_39,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X3)
    | ~ r1_xboole_0(X3,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r1_xboole_0(X1,k1_relat_1(esk10_0))
    | ~ r2_hidden(esk1_2(X1,k1_relat_1(esk10_0)),esk9_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k9_relat_1(esk10_0,esk9_0) != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(esk10_0),esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r1_xboole_0(esk9_0,k1_relat_1(esk10_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(esk10_0),esk9_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42,c_0_34])])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.77/0.94  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.77/0.94  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.77/0.94  #
% 0.77/0.94  # Preprocessing time       : 0.029 s
% 0.77/0.94  
% 0.77/0.94  # Proof found!
% 0.77/0.94  # SZS status Theorem
% 0.77/0.94  # SZS output start CNFRefutation
% 0.77/0.94  fof(d13_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X5,X4),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 0.77/0.94  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 0.77/0.94  fof(t148_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>k2_relat_1(k7_relat_1(X2,X1))=k9_relat_1(X2,X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 0.77/0.94  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 0.77/0.94  fof(t151_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 0.77/0.94  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.77/0.94  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.77/0.94  fof(t2_boole, axiom, ![X1]:k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 0.77/0.94  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.77/0.94  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.77/0.94  fof(c_0_10, plain, ![X20, X21, X22, X23, X25, X26, X27, X28, X30]:((((r2_hidden(k4_tarski(esk3_4(X20,X21,X22,X23),X23),X20)|~r2_hidden(X23,X22)|X22!=k9_relat_1(X20,X21)|~v1_relat_1(X20))&(r2_hidden(esk3_4(X20,X21,X22,X23),X21)|~r2_hidden(X23,X22)|X22!=k9_relat_1(X20,X21)|~v1_relat_1(X20)))&(~r2_hidden(k4_tarski(X26,X25),X20)|~r2_hidden(X26,X21)|r2_hidden(X25,X22)|X22!=k9_relat_1(X20,X21)|~v1_relat_1(X20)))&((~r2_hidden(esk4_3(X20,X27,X28),X28)|(~r2_hidden(k4_tarski(X30,esk4_3(X20,X27,X28)),X20)|~r2_hidden(X30,X27))|X28=k9_relat_1(X20,X27)|~v1_relat_1(X20))&((r2_hidden(k4_tarski(esk5_3(X20,X27,X28),esk4_3(X20,X27,X28)),X20)|r2_hidden(esk4_3(X20,X27,X28),X28)|X28=k9_relat_1(X20,X27)|~v1_relat_1(X20))&(r2_hidden(esk5_3(X20,X27,X28),X27)|r2_hidden(esk4_3(X20,X27,X28),X28)|X28=k9_relat_1(X20,X27)|~v1_relat_1(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_relat_1])])])])])])).
% 0.77/0.94  fof(c_0_11, plain, ![X32, X33, X34, X36, X37, X38, X39, X41]:(((~r2_hidden(X34,X33)|r2_hidden(k4_tarski(X34,esk6_3(X32,X33,X34)),X32)|X33!=k1_relat_1(X32))&(~r2_hidden(k4_tarski(X36,X37),X32)|r2_hidden(X36,X33)|X33!=k1_relat_1(X32)))&((~r2_hidden(esk7_2(X38,X39),X39)|~r2_hidden(k4_tarski(esk7_2(X38,X39),X41),X38)|X39=k1_relat_1(X38))&(r2_hidden(esk7_2(X38,X39),X39)|r2_hidden(k4_tarski(esk7_2(X38,X39),esk8_2(X38,X39)),X38)|X39=k1_relat_1(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.77/0.94  fof(c_0_12, plain, ![X43, X44]:(~v1_relat_1(X44)|k2_relat_1(k7_relat_1(X44,X43))=k9_relat_1(X44,X43)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t148_relat_1])])).
% 0.77/0.94  fof(c_0_13, plain, ![X45, X46]:((k7_relat_1(X46,X45)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X46),X45)|~v1_relat_1(X46))&(~r1_xboole_0(k1_relat_1(X46),X45)|k7_relat_1(X46,X45)=k1_xboole_0|~v1_relat_1(X46))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.77/0.94  fof(c_0_14, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k9_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t151_relat_1])).
% 0.77/0.94  cnf(c_0_15, plain, (r2_hidden(X2,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X1,X4)|X5!=k9_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.77/0.94  cnf(c_0_16, plain, (r2_hidden(k4_tarski(X1,esk6_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.77/0.94  cnf(c_0_17, plain, (k2_relat_1(k7_relat_1(X1,X2))=k9_relat_1(X1,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.77/0.94  cnf(c_0_18, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.77/0.94  cnf(c_0_19, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.77/0.94  fof(c_0_20, negated_conjecture, (v1_relat_1(esk10_0)&((k9_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk10_0),esk9_0))&(k9_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk10_0),esk9_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).
% 0.77/0.94  fof(c_0_21, plain, ![X12, X13, X15, X16, X17]:((r1_xboole_0(X12,X13)|r2_hidden(esk2_2(X12,X13),k3_xboole_0(X12,X13)))&(~r2_hidden(X17,k3_xboole_0(X15,X16))|~r1_xboole_0(X15,X16))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.77/0.94  fof(c_0_22, plain, ![X18]:k3_xboole_0(X18,k1_xboole_0)=k1_xboole_0, inference(variable_rename,[status(thm)],[t2_boole])).
% 0.77/0.94  fof(c_0_23, plain, ![X19]:r1_xboole_0(X19,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.77/0.94  cnf(c_0_24, plain, (r2_hidden(X1,k9_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X4,X1),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_15])).
% 0.77/0.94  cnf(c_0_25, plain, (r2_hidden(k4_tarski(X1,esk6_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_16])).
% 0.77/0.94  cnf(c_0_26, plain, (k9_relat_1(X1,X2)=k1_xboole_0|~v1_relat_1(X1)|~r1_xboole_0(k1_relat_1(X1),X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])).
% 0.77/0.94  cnf(c_0_27, negated_conjecture, (k9_relat_1(esk10_0,esk9_0)=k1_xboole_0|r1_xboole_0(k1_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.94  cnf(c_0_28, negated_conjecture, (v1_relat_1(esk10_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.94  cnf(c_0_29, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.77/0.94  cnf(c_0_30, plain, (k3_xboole_0(X1,k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.77/0.94  cnf(c_0_31, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.77/0.94  fof(c_0_32, plain, ![X6, X7, X9, X10, X11]:(((r2_hidden(esk1_2(X6,X7),X6)|r1_xboole_0(X6,X7))&(r2_hidden(esk1_2(X6,X7),X7)|r1_xboole_0(X6,X7)))&(~r2_hidden(X11,X9)|~r2_hidden(X11,X10)|~r1_xboole_0(X9,X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.77/0.94  cnf(c_0_33, plain, (r2_hidden(esk6_3(X1,k1_relat_1(X1),X2),k9_relat_1(X1,X3))|~v1_relat_1(X1)|~r2_hidden(X2,k1_relat_1(X1))|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.77/0.94  cnf(c_0_34, negated_conjecture, (k9_relat_1(esk10_0,esk9_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])])).
% 0.77/0.94  cnf(c_0_35, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])])).
% 0.77/0.94  cnf(c_0_36, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.94  cnf(c_0_37, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.94  cnf(c_0_38, negated_conjecture, (~r2_hidden(X1,k1_relat_1(esk10_0))|~r2_hidden(X1,esk9_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_28])]), c_0_35])).
% 0.77/0.94  cnf(c_0_39, plain, (r2_hidden(esk1_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.77/0.94  cnf(c_0_40, plain, (r1_xboole_0(X1,X2)|~r2_hidden(esk1_2(X1,X2),X3)|~r1_xboole_0(X3,X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.77/0.94  cnf(c_0_41, negated_conjecture, (r1_xboole_0(X1,k1_relat_1(esk10_0))|~r2_hidden(esk1_2(X1,k1_relat_1(esk10_0)),esk9_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.77/0.94  cnf(c_0_42, negated_conjecture, (k9_relat_1(esk10_0,esk9_0)!=k1_xboole_0|~r1_xboole_0(k1_relat_1(esk10_0),esk9_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.77/0.94  cnf(c_0_43, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X2,X1)), inference(spm,[status(thm)],[c_0_40, c_0_39])).
% 0.77/0.94  cnf(c_0_44, negated_conjecture, (r1_xboole_0(esk9_0,k1_relat_1(esk10_0))), inference(spm,[status(thm)],[c_0_41, c_0_37])).
% 0.77/0.94  cnf(c_0_45, negated_conjecture, (~r1_xboole_0(k1_relat_1(esk10_0),esk9_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_42, c_0_34])])).
% 0.77/0.94  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45]), ['proof']).
% 0.77/0.94  # SZS output end CNFRefutation
% 0.77/0.94  # Proof object total steps             : 47
% 0.77/0.94  # Proof object clause steps            : 27
% 0.77/0.94  # Proof object formula steps           : 20
% 0.77/0.94  # Proof object conjectures             : 12
% 0.77/0.94  # Proof object clause conjectures      : 9
% 0.77/0.94  # Proof object formula conjectures     : 3
% 0.77/0.94  # Proof object initial clauses used    : 14
% 0.77/0.94  # Proof object initial formulas used   : 10
% 0.77/0.94  # Proof object generating inferences   : 10
% 0.77/0.94  # Proof object simplifying inferences  : 13
% 0.77/0.94  # Training examples: 0 positive, 0 negative
% 0.77/0.94  # Parsed axioms                        : 10
% 0.77/0.94  # Removed by relevancy pruning/SinE    : 0
% 0.77/0.94  # Initial clauses                      : 25
% 0.77/0.94  # Removed in clause preprocessing      : 0
% 0.77/0.94  # Initial clauses in saturation        : 25
% 0.77/0.94  # Processed clauses                    : 11253
% 0.77/0.94  # ...of these trivial                  : 0
% 0.77/0.94  # ...subsumed                          : 10589
% 0.77/0.94  # ...remaining for further processing  : 664
% 0.77/0.94  # Other redundant clauses eliminated   : 5
% 0.77/0.94  # Clauses deleted for lack of memory   : 0
% 0.77/0.94  # Backward-subsumed                    : 20
% 0.77/0.94  # Backward-rewritten                   : 5
% 0.77/0.94  # Generated clauses                    : 55641
% 0.77/0.94  # ...of the previous two non-trivial   : 51954
% 0.77/0.94  # Contextual simplify-reflections      : 9
% 0.77/0.94  # Paramodulations                      : 55634
% 0.77/0.94  # Factorizations                       : 2
% 0.77/0.94  # Equation resolutions                 : 5
% 0.77/0.94  # Propositional unsat checks           : 0
% 0.77/0.94  #    Propositional check models        : 0
% 0.77/0.94  #    Propositional check unsatisfiable : 0
% 0.77/0.94  #    Propositional clauses             : 0
% 0.77/0.94  #    Propositional clauses after purity: 0
% 0.77/0.94  #    Propositional unsat core size     : 0
% 0.77/0.94  #    Propositional preprocessing time  : 0.000
% 0.77/0.94  #    Propositional encoding time       : 0.000
% 0.77/0.94  #    Propositional solver time         : 0.000
% 0.77/0.94  #    Success case prop preproc time    : 0.000
% 0.77/0.94  #    Success case prop encoding time   : 0.000
% 0.77/0.94  #    Success case prop solver time     : 0.000
% 0.77/0.94  # Current number of processed clauses  : 634
% 0.77/0.94  #    Positive orientable unit clauses  : 10
% 0.77/0.94  #    Positive unorientable unit clauses: 0
% 0.77/0.94  #    Negative unit clauses             : 2
% 0.77/0.94  #    Non-unit-clauses                  : 622
% 0.77/0.94  # Current number of unprocessed clauses: 40441
% 0.77/0.94  # ...number of literals in the above   : 144279
% 0.77/0.94  # Current number of archived formulas  : 0
% 0.77/0.94  # Current number of archived clauses   : 25
% 0.77/0.94  # Clause-clause subsumption calls (NU) : 154417
% 0.77/0.94  # Rec. Clause-clause subsumption calls : 129067
% 0.77/0.94  # Non-unit clause-clause subsumptions  : 9371
% 0.77/0.94  # Unit Clause-clause subsumption calls : 56
% 0.77/0.94  # Rewrite failures with RHS unbound    : 0
% 0.77/0.94  # BW rewrite match attempts            : 3
% 0.77/0.94  # BW rewrite match successes           : 3
% 0.77/0.94  # Condensation attempts                : 0
% 0.77/0.94  # Condensation successes               : 0
% 0.77/0.94  # Termbank termtop insertions          : 844115
% 0.77/0.94  
% 0.77/0.94  # -------------------------------------------------
% 0.77/0.94  # User time                : 0.572 s
% 0.77/0.94  # System time              : 0.027 s
% 0.77/0.94  # Total time               : 0.599 s
% 0.77/0.94  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
